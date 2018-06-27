/*
 * Copyright 2018 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.gradle.integtests.resolve.caching

import org.gradle.api.file.FileVisitDetails
import org.gradle.api.file.FileVisitor
import org.gradle.api.internal.artifacts.ivyservice.CacheLayout
import org.gradle.integtests.fixtures.cache.FileAccessTimeJournalFixture
import org.gradle.api.internal.file.collections.SingleIncludePatternFileTree
import org.gradle.cache.internal.LeastRecentlyUsedCacheCleanup
import org.gradle.integtests.fixtures.AbstractHttpDependencyResolutionTest
import org.gradle.integtests.resolve.JvmLibraryArtifactResolveTestFixture
import org.gradle.test.fixtures.file.TestFile
import org.gradle.test.fixtures.maven.MavenModule

import static java.util.concurrent.TimeUnit.DAYS

class DefaultCacheLockingManagerIntegrationTest extends AbstractHttpDependencyResolutionTest implements FileAccessTimeJournalFixture {
    private final static long MAX_CACHE_AGE_IN_DAYS = LeastRecentlyUsedCacheCleanup.DEFAULT_MAX_AGE_IN_DAYS_FOR_EXTERNAL_CACHE_ENTRIES

    def snapshotModule = mavenHttpRepo.module('org.example', 'example', '1.0-SNAPSHOT').publish().allowAll()

    def setup() {
        requireOwnGradleUserHomeDir()
    }

    def "does not clean up resources and files that were recently used from caches"() {
        given:
        buildscriptWithDependency(snapshotModule)

        when:
        succeeds 'resolve'

        then:
        def resource = findFile(cacheDir, 'resources-*/**/maven-metadata.xml')
        def files = findFiles(cacheDir, "files-*/**/*")
        files.size() == 2

        when:
        markForCleanup(gcFile)

        and:
        succeeds 'tasks'

        then:
        resource.assertExists()
        files[0].assertExists()
        files[1].assertExists()
    }

    def "cleans up resources and files that were not recently used from caches"() {
        given:
        buildscriptWithDependency(snapshotModule)

        when:
        executer.requireIsolatedDaemons() // needs to stop daemon
        requireOwnGradleUserHomeDir() // needs its own journal
        succeeds 'resolve'

        then:
        def resource = findFile(cacheDir, 'resources-*/**/maven-metadata.xml')
        def files = findFiles(cacheDir, "files-*/**/*")
        files.size() == 2
        journal.assertExists()

        when:
        run '--stop' // ensure daemon does not cache file access times in memory
        assert journal.delete() // delete journal to clear access time information
        markForCleanup(gcFile) // force cleanup

        and: // last modified timestamp is used when journal does not exist
        markForCleanup(resource.parentFile)
        markForCleanup(files[0].parentFile)
        markForCleanup(files[1].parentFile)

        and:
        // start as new process so journal is not restored from in-memory cache
        executer.withTasks('tasks').start().waitForFinish()

        then:
        resource.assertDoesNotExist()
        files[0].assertDoesNotExist()
        files[1].assertDoesNotExist()
    }

    def "downloads deleted files again when they are referenced"() {
        given:
        buildscriptWithDependency(snapshotModule)

        when:
        succeeds 'resolve'

        then:
        def jarFile = findFile(cacheDir, "files-*/**/*.jar")

        when:
        assert jarFile.delete()

        and:
        succeeds 'resolve'

        then:
        jarFile.assertExists()
    }

    def "marks artifacts as recently used when accessed"() {
        given:
        buildscriptWithDependency(snapshotModule)

        when:
        requireOwnGradleUserHomeDir() // needs its own journal
        succeeds 'resolve'

        and:
        journal.delete()

        then:
        succeeds 'resolve'

        and:
        journal.assertExists()
    }

    def "redownloads deleted HTTP script plugin resources"() {
        given:
        def uuid = UUID.randomUUID()
        def uniqueFileName = "external-${uuid}.gradle"
        def script = file(uniqueFileName) << """
            task customTask
        """
        buildFile << """
            apply from: '$server.uri/$uniqueFileName'
            defaultTasks 'customTask'
        """
        server.expectGet("/$uniqueFileName", script)

        when:
        succeeds()

        then:
        def resource = findFile(cacheDir, "resources-*/**/$uniqueFileName")

        when:
        assert resource.delete()
        server.expectGet("/$uniqueFileName", script)

        and:
        succeeds()

        then:
        resource.assertExists()
    }

    def "redownloads deleted uri backed text resources"() {
        given:
        def uuid = UUID.randomUUID()
        def resourceFile = file("test.txt") << "Hello, Gradle!"
        def uniqueFileName = "my-uri-text-resource-${uuid}.txt"
        server.expectGet("/$uniqueFileName", resourceFile)
        buildFile << """
            task uriText {
                doLast {
                    print resources.text.fromUri("http://localhost:$server.port/$uniqueFileName").asString()
                }
            }
        """

        when:
        succeeds 'uriText'

        then:
        def resource = findFile(cacheDir, "resources-*/**/$uniqueFileName")

        when:
        assert resource.delete()
        server.expectGet("/$uniqueFileName", resourceFile)

        and:
        succeeds 'uriText'

        then:
        resource.assertExists()
    }

    def "redownloads deleted artifacts for artifact query"() {
        given:
        def module = mavenHttpRepo.module('org.example', 'example', '1.0')
        def sourceArtifact = module.artifact(classifier: "sources")
        module.publish()
        buildFile.text = """
            repositories {
                maven { url '$mavenHttpRepo.uri' }
            }
        """

        and:
        new JvmLibraryArtifactResolveTestFixture(buildFile)
            .withComponentVersion('org.example', 'example', '1.0')
            .requestingSource()
            .expectSourceArtifact("sources")
            .prepare()

        when:
        module.pom.expectGet()
        sourceArtifact.expectHead()
        sourceArtifact.expectGet()

        then:
        succeeds 'verify'

        and:
        def jarFile = findFile(cacheDir, "files-*/**/example-1.0-sources.jar")

        when:
        assert jarFile.delete()
        server.resetExpectations()
        sourceArtifact.expectGet()

        then:
        succeeds 'verify'

        and:
        jarFile.assertExists()
    }

    private static TestFile findFile(File baseDir, String includePattern) {
        List<TestFile> files = findFiles(baseDir, includePattern)
        assert files.size() == 1
        return files[0]
    }

    private static List<TestFile> findFiles(File baseDir, String includePattern) {
        List<TestFile> files = []
        new SingleIncludePatternFileTree(baseDir, includePattern).visit(new FileVisitor() {
            @Override
            void visitDir(FileVisitDetails dirDetails) {
            }

            @Override
            void visitFile(FileVisitDetails fileDetails) {
                files.add(new TestFile(fileDetails.file))
            }
        })
        return files
    }

    private void buildscriptWithDependency(MavenModule module) {
        buildFile.text = """
            repositories {
                maven { url = '${mavenHttpRepo.uri}' }
            }
            configurations {
                custom
            }
            dependencies {
                custom group: '${module.groupId}', name: '${module.artifactId}', version: '${module.version}'
            }
            task resolve {
                doLast {
                    configurations.custom.incoming.files.each { println it }
                }
            }
        """
    }

    TestFile getGcFile() {
        return cacheDir.file("gc.properties")
    }

    TestFile getCacheDir() {
        return getUserHomeCacheDir().file(CacheLayout.ROOT.getKey())
    }

    void markForCleanup(File file) {
        file.lastModified = System.currentTimeMillis() - DAYS.toMillis(MAX_CACHE_AGE_IN_DAYS + 1)
    }
}