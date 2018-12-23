/*
 * Copyright 2010 the original author or authors.
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

package org.gradle.api.internal;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.SetMultimap;
import groovy.lang.Closure;
import groovy.lang.GroovyObject;
import org.apache.commons.collections.map.AbstractReferenceMap;
import org.apache.commons.collections.map.ReferenceMap;
import org.gradle.api.Action;
import org.gradle.api.NonExtensible;
import org.gradle.api.plugins.ExtensionAware;
import org.gradle.api.provider.HasMultipleValues;
import org.gradle.api.provider.MapProperty;
import org.gradle.api.provider.Property;
import org.gradle.internal.reflect.ClassDetails;
import org.gradle.internal.reflect.ClassInspector;
import org.gradle.internal.reflect.JavaReflectionUtil;
import org.gradle.internal.reflect.PropertyAccessorType;
import org.gradle.internal.reflect.PropertyDetails;
import org.gradle.internal.service.ServiceRegistry;

import javax.annotation.Nullable;
import javax.inject.Inject;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Generates a subclass of the target class to mix-in some DSL behaviour.
 *
 * <ul>
 *     <li>For each property, a convention mapping is applied. These properties may have a setter method.</li>
 *     <li>For each property whose getter is annotated with {@code Inject}, a service instance will be injected instead. These properties may have a setter method.</li>
 *     <li>For each mutable property as set method is generated.</li>
 *     <li>For each method whose last parameter is an {@link org.gradle.api.Action}, an override is generated that accepts a {@link groovy.lang.Closure} instead.</li>
 *     <li>Coercion from string to enum property is mixed in.</li>
 *     <li>{@link groovy.lang.GroovyObject} is mixed in to the class.</li>
 * </ul>
 */
public abstract class AbstractClassGenerator implements ClassGenerator {
    private static final Map<Class<?>, Map<Class<?>, Class<?>>> GENERATED_CLASSES = new HashMap<Class<?>, Map<Class<?>, Class<?>>>();
    private static final Lock CACHE_LOCK = new ReentrantLock();
    private static final Collection<String> SKIP_PROPERTIES = Arrays.asList("class", "metaClass", "conventionMapping", "convention", "asDynamicObject", "extensions");

    public <T> Class<? extends T> generate(Class<T> type) {
        CACHE_LOCK.lock();
        try {
            return generateUnderLock(type);
        } finally {
            CACHE_LOCK.unlock();
        }
    }

    private <T> Class<? extends T> generateUnderLock(Class<T> type) {
        Map<Class<?>, Class<?>> cache = GENERATED_CLASSES.get(getClass());
        if (cache == null) {
            // WeakHashMap won't work here. It keeps a strong reference to the mapping value, which is the generated class in this case
            // However, the generated class has a strong reference to the source class (by extending it), so the keys will always be
            // strongly reachable while this Class is strongly reachable. Use weak references for both key and value of the mapping instead.
            cache = new ReferenceMap(AbstractReferenceMap.WEAK, AbstractReferenceMap.WEAK);
            GENERATED_CLASSES.put(getClass(), cache);
        }
        Class<?> generatedClass = cache.get(type);
        if (generatedClass != null) {
            return generatedClass.asSubclass(type);
        }

        Class<? extends T> subclass;
        try {
            ServiceInjectionPropertyHandler injectionHandler = new ServiceInjectionPropertyHandler();
            ExtensionAwarePropertyHandler extensionHandler = new ExtensionAwarePropertyHandler();
            List<PropertyHandler> handlers = ImmutableList.of(extensionHandler, injectionHandler);
            List<PropertyMetaData> unclaimedProperties = new ArrayList<PropertyMetaData>();
            ClassMetaData classMetaData = inspectType(type, handlers, unclaimedProperties);
            classMetaData.shouldImplementWithServiceRegistry = injectionHandler.isShouldImplementWithServicesRegistry();

            ClassBuilder<T> builder = start(type, classMetaData);

            if (!DynamicObjectAware.class.isAssignableFrom(type)) {
                builder.mixInDynamicAware();
            }
            if (!GroovyObject.class.isAssignableFrom(type)) {
                builder.mixInGroovyObject();
            }
            builder.addDynamicMethods();
            if (classMetaData.conventionAware && !IConventionAware.class.isAssignableFrom(type)) {
                builder.mixInConventionAware();
            }

            Class noMappingClass = Object.class;
            for (Class<?> c = type; c != null && noMappingClass == Object.class; c = c.getSuperclass()) {
                if (c.getAnnotation(NoConventionMapping.class) != null) {
                    noMappingClass = c;
                }
            }

            for (PropertyHandler handler : handlers) {
                handler.generate(builder);
            }

            Set<PropertyMetaData> conventionProperties = new HashSet<PropertyMetaData>();

            for (PropertyMetaData property : unclaimedProperties) {
                if (SKIP_PROPERTIES.contains(property.name)) {
                    continue;
                }

                if (property.isReadable() && isModelProperty(property)) {
                    builder.addPropertySetters(property, property.mainGetter);
                    continue;
                }

                // TODO - extract more

                boolean needsConventionMapping = false;
                if (classMetaData.isExtensible()) {
                    for (Method getter : property.getOverridableGetters()) {
                        if (!getter.getDeclaringClass().isAssignableFrom(noMappingClass)) {
                            needsConventionMapping = true;
                            break;
                        }
                    }
                }

                if (needsConventionMapping) {
                    conventionProperties.add(property);
                    builder.addConventionProperty(property);
                    for (Method getter : property.getOverridableGetters()) {
                        builder.applyConventionMappingToGetter(property, getter);
                    }

                    for (Method setter : property.getOverridableSetters()) {
                        builder.applyConventionMappingToSetter(property, setter);
                    }
                }
            }

            Set<Method> actionMethods = classMetaData.missingOverloads;
            for (Method method : actionMethods) {
                builder.addActionMethod(method);
            }

            // Adds a set method for each mutable property
            for (PropertyMetaData property : classMetaData.properties.values()) {
                if (property.setters.isEmpty()) {
                    continue;
                }
                if (Iterable.class.isAssignableFrom(property.getType())) {
                    // Currently not supported
                    continue;
                }

                if (property.setMethods.isEmpty()) {
                    for (Method setter : property.setters) {
                        builder.addSetMethod(property, setter);
                    }
                } else if (conventionProperties.contains(property)) {
                    for (Method setMethod : property.setMethods) {
                        builder.applyConventionMappingToSetMethod(property, setMethod);
                    }
                }
            }

            for (Constructor<?> constructor : type.getConstructors()) {
                if (Modifier.isPublic(constructor.getModifiers())) {
                    builder.addConstructor(constructor);
                }
            }

            subclass = builder.generate();
        } catch (ClassGenerationException e) {
            throw e;
        } catch (Throwable e) {
            throw new ClassGenerationException(String.format("Could not generate a decorated class for class %s.", type.getName()), e);
        }

        cache.put(type, subclass);
        cache.put(subclass, subclass);
        return subclass;
    }

    private boolean isModelProperty(PropertyMetaData property) {
        return Property.class.isAssignableFrom(property.getType()) ||
            HasMultipleValues.class.isAssignableFrom(property.getType()) ||
            MapProperty.class.isAssignableFrom(property.getType());
    }

    protected abstract <T> ClassBuilder<T> start(Class<T> type, ClassMetaData classMetaData);

    private ClassMetaData inspectType(Class<?> type, List<PropertyHandler> propertyHandlers, List<PropertyMetaData> unclaimedProperties) {
        boolean isConventionAware = type.getAnnotation(NoConventionMapping.class) == null;
        boolean extensible = JavaReflectionUtil.getAnnotation(type, NonExtensible.class) == null;

        ClassMetaData classMetaData = new ClassMetaData(extensible, isConventionAware);
        inspectType(type, classMetaData, propertyHandlers, unclaimedProperties);
        attachSetMethods(classMetaData);
        findMissingClosureOverloads(classMetaData);
        classMetaData.complete();
        return classMetaData;
    }

    private void findMissingClosureOverloads(ClassMetaData classMetaData) {
        for (Method method : classMetaData.actionMethods) {
            Method overload = findClosureOverload(method, classMetaData.closureMethods.get(method.getName()));
            if (overload == null) {
                classMetaData.actionMethodRequiresOverload(method);
            }
        }
    }

    @Nullable
    private Method findClosureOverload(Method method, Collection<Method> candidates) {
        for (Method candidate : candidates) {
            if (candidate.getParameterTypes().length != method.getParameterTypes().length) {
                continue;
            }
            boolean matches = true;
            for (int i = 0; matches && i < candidate.getParameterTypes().length - 1; i++) {
                if (!candidate.getParameterTypes()[i].equals(method.getParameterTypes()[i])) {
                    matches = false;
                }
            }
            if (matches) {
                return candidate;
            }
        }
        return null;
    }

    private void attachSetMethods(ClassMetaData classMetaData) {
        for (Method method : classMetaData.setMethods) {
            PropertyMetaData property = classMetaData.getProperty(method.getName());
            if (property != null) {
                property.addSetMethod(method);
            }
        }
    }

    private void inspectType(Class<?> type, ClassMetaData classMetaData, List<PropertyHandler> propertyHandlers, List<PropertyMetaData> unclaimedProperties) {
        ClassDetails classDetails = ClassInspector.inspect(type);
        for (Method method : classDetails.getAllMethods()) {
            for (PropertyHandler propertyHandler : propertyHandlers) {
                propertyHandler.validateMethod(method);
            }
        }

        for (PropertyDetails property : classDetails.getProperties()) {
            PropertyMetaData propertyMetaData = classMetaData.property(property.getName());
            for (Method method : property.getGetters()) {
                propertyMetaData.addGetter(method);
            }
            for (Method method : property.getSetters()) {
                propertyMetaData.addSetter(method);
            }
            PropertyHandler ownedBy = null;
            for (PropertyHandler propertyHandler : propertyHandlers) {
                if (!propertyHandler.claimProperty(propertyMetaData)) {
                    continue;
                }
                if (ownedBy == null) {
                    ownedBy = propertyHandler;
                } else {
                    propertyHandler.ambiguous(propertyMetaData);
                }
            }
            if (ownedBy != null) {
                continue;
            }
            unclaimedProperties.add(propertyMetaData);
            for (Method method : property.getGetters()) {
                if (!method.getDeclaringClass().equals(ExtensionAware.class)) {
                    assertNotAbstract(type, method);
                }
            }
            for (Method method : property.getSetters()) {
                assertNotAbstract(type, method);
            }
        }

        for (Method method : classDetails.getInstanceMethods()) {
            assertNotAbstract(type, method);
            Class<?>[] parameterTypes = method.getParameterTypes();
            if (parameterTypes.length == 1) {
                classMetaData.addCandidateSetMethod(method);
            }
            if (parameterTypes.length > 0 && parameterTypes[parameterTypes.length - 1].equals(Action.class)) {
                classMetaData.addActionMethod(method);
            } else if (parameterTypes.length > 0 && parameterTypes[parameterTypes.length - 1].equals(Closure.class)) {
                classMetaData.addClosureMethod(method);
            }
        }
    }

    private void assertNotAbstract(Class<?> type, Method method) {
        if (Modifier.isAbstract(type.getModifiers()) && Modifier.isAbstract(method.getModifiers())) {
            throw new IllegalArgumentException(String.format("Cannot have abstract method %s.%s().", method.getDeclaringClass().getSimpleName(), method.getName()));
        }
        // Else, ignore abstract methods on non-abstract classes as some other tooling (e.g. the Groovy compiler) has decided this is ok
    }

    protected static class ClassMetaData {
        private final Map<String, PropertyMetaData> properties = new LinkedHashMap<String, PropertyMetaData>();
        private final Set<Method> missingOverloads = new LinkedHashSet<Method>();
        private final boolean extensible;
        private final boolean conventionAware;

        private List<Method> actionMethods = new ArrayList<Method>();
        private SetMultimap<String, Method> closureMethods = LinkedHashMultimap.create();
        private List<Method> setMethods = new ArrayList<Method>();
        private boolean shouldImplementWithServiceRegistry;

        public ClassMetaData(boolean extensible, boolean conventionAware) {
            this.extensible = extensible;
            this.conventionAware = conventionAware;
        }

        @Nullable
        public PropertyMetaData getProperty(String name) {
            return properties.get(name);
        }

        public PropertyMetaData property(String name) {
            PropertyMetaData property = properties.get(name);
            if (property == null) {
                property = new PropertyMetaData(name);
                properties.put(name, property);
            }
            return property;
        }

        public void addActionMethod(Method method) {
            actionMethods.add(method);
        }

        public void addClosureMethod(Method method) {
            closureMethods.put(method.getName(), method);
        }

        public void addCandidateSetMethod(Method method) {
            setMethods.add(method);
        }

        public void complete() {
            setMethods = null;
            actionMethods = null;
            closureMethods = null;
        }

        public void actionMethodRequiresOverload(Method method) {
            missingOverloads.add(method);
        }

        public boolean providesDynamicObjectImplementation() {
            PropertyMetaData property = properties.get("asDynamicObject");
            return property != null && property.isReadable();
        }

        public boolean isExtensible() {
            return extensible;
        }

        public boolean isConventionAware() {
            return conventionAware;
        }

        public boolean isShouldImplementWithServiceRegistry() {
            return shouldImplementWithServiceRegistry;
        }
    }

    protected static class PropertyMetaData {
        private final String name;
        private final List<Method> getters = new ArrayList<Method>();
        private final List<Method> overridableGetters = new ArrayList<Method>();
        private final List<Method> overridableSetters = new ArrayList<Method>();
        private final List<Method> setters = new ArrayList<Method>();
        private final List<Method> setMethods = new ArrayList<Method>();
        private Method mainGetter;

        private PropertyMetaData(String name) {
            this.name = name;
        }

        @Override
        public String toString() {
            return "[property " + name + "]";
        }

        public String getName() {
            return name;
        }

        public boolean isReadable() {
            return mainGetter != null;
        }

        public Iterable<Method> getOverridableGetters() {
            return overridableGetters;
        }

        public Iterable<Method> getOverridableSetters() {
            return overridableSetters;
        }

        public Class<?> getType() {
            if (mainGetter != null) {
                return mainGetter.getReturnType();
            }
            return setters.get(0).getParameterTypes()[0];
        }

        public Type getGenericType() {
            if (mainGetter != null) {
                return mainGetter.getGenericReturnType();
            }
            return setters.get(0).getGenericParameterTypes()[0];
        }

        public void addGetter(Method method) {
            if (!Modifier.isFinal(method.getModifiers()) && !method.isBridge()) {
                overridableGetters.add(method);
            }
            getters.add(method);
            if (mainGetter == null) {
                mainGetter = method;
            } else if (mainGetter.isBridge() && !method.isBridge()) {
                mainGetter = method;
            }
        }

        public void addSetter(Method method) {
            for (Method setter : setters) {
                if (setter.getParameterTypes()[0].equals(method.getParameterTypes()[0])) {
                    return;
                }
            }
            setters.add(method);
            if (!Modifier.isFinal(method.getModifiers()) && !method.isBridge()) {
                overridableSetters.add(method);
            }
        }

        public void addSetMethod(Method method) {
            setMethods.add(method);
        }
    }

    private static class PropertyHandler {
        /**
         * Called for each method of the type, before any other methods are called.
         */
        void validateMethod(Method method) {
        }

        /**
         * Handler can claim the property, taking responsibility for generating whatever is required to make the property work.
         * Handler is also expected to take care of validation.
         */
        boolean claimProperty(PropertyMetaData propertyMetaData) {
            return false;
        }

        void generate(ClassBuilder<?> builder) {
        }

        void ambiguous(PropertyMetaData propertyMetaData) {
            throw new UnsupportedOperationException("Multiple matches for " + propertyMetaData.getName());
        }
    }

    private static class ExtensionAwarePropertyHandler extends PropertyHandler {
        private boolean hasExtensionAwareImplementation;

        @Override
        boolean claimProperty(PropertyMetaData propertyMetaData) {
            if (propertyMetaData.getName().equals("extensions")) {
                for (Method getter : propertyMetaData.getOverridableGetters()) {
                    if (Modifier.isAbstract(getter.getModifiers())) {
                        return true;
                    }
                }
                hasExtensionAwareImplementation = true;
                return true;
            }
            return false;
        }
    }

    private static class ServiceInjectionPropertyHandler extends PropertyHandler {
        private boolean hasServicesProperty;
        private final Set<PropertyMetaData> serviceInjectionProperties = new HashSet<PropertyMetaData>();

        @Override
        public void validateMethod(Method method) {
            if (method.getAnnotation(Inject.class) != null) {
                if (Modifier.isStatic(method.getModifiers())) {
                    throw new UnsupportedOperationException(String.format("Cannot attach @Inject to method %s.%s() as it is static.", method.getDeclaringClass().getSimpleName(), method.getName()));
                }
                if (PropertyAccessorType.of(method) != PropertyAccessorType.GET_GETTER) {
                    throw new UnsupportedOperationException(String.format("Cannot attach @Inject to method %s.%s() as it is not a property getter.", method.getDeclaringClass().getSimpleName(), method.getName()));
                }
                if (Modifier.isFinal(method.getModifiers())) {
                    throw new UnsupportedOperationException(String.format("Cannot attach @Inject to method %s.%s() as it is final.", method.getDeclaringClass().getSimpleName(), method.getName()));
                }
                if (!Modifier.isPublic(method.getModifiers()) && !Modifier.isProtected(method.getModifiers())) {
                    throw new UnsupportedOperationException(String.format("Cannot attach @Inject to method %s.%s() as it is not public or protected.", method.getDeclaringClass().getSimpleName(), method.getName()));
                }
            }
        }

        @Override
        public boolean claimProperty(PropertyMetaData propertyMetaData) {
            if (propertyMetaData.getName().equals("services") && propertyMetaData.isReadable() && ServiceRegistry.class.isAssignableFrom(propertyMetaData.getType())) {
                hasServicesProperty = true;
                return true;
            }
            for (Method method : propertyMetaData.getters) {
                if (method.getAnnotation(Inject.class) != null) {
                    serviceInjectionProperties.add(propertyMetaData);
                    return true;
                }
            }
            return false;
        }

        @Override
        void ambiguous(PropertyMetaData propertyMetaData) {
            for (Method method : propertyMetaData.getters) {
                if (method.getAnnotation(Inject.class) != null) {
                    throw new IllegalArgumentException(String.format("Cannot use @Inject annotation on method %s.%s().", method.getDeclaringClass().getSimpleName(), method.getName()));
                }
            }
            super.ambiguous(propertyMetaData);
        }

        @Override
        public void generate(ClassBuilder<?> builder) {
            if (isShouldImplementWithServicesRegistry()) {
                builder.generateServiceRegistrySupportMethods();
            }
            for (PropertyMetaData property : serviceInjectionProperties) {
                builder.addInjectorProperty(property);
                for (Method getter : property.getOverridableGetters()) {
                    builder.applyServiceInjectionToGetter(property, getter);
                }
                for (Method setter : property.getOverridableSetters()) {
                    builder.applyServiceInjectionToSetter(property, setter);
                }
            }
        }

        public boolean isShouldImplementWithServicesRegistry() {
            return !serviceInjectionProperties.isEmpty() && !hasServicesProperty;
        }
    }

    protected interface ClassBuilder<T> {
        void addConstructor(Constructor<?> constructor) throws Exception;

        void mixInDynamicAware() throws Exception;

        void mixInConventionAware() throws Exception;

        void mixInGroovyObject() throws Exception;

        void addDynamicMethods() throws Exception;

        void addInjectorProperty(PropertyMetaData property);

        void applyServiceInjectionToGetter(PropertyMetaData property, Method getter);

        void applyServiceInjectionToSetter(PropertyMetaData property, Method setter);

        void addConventionProperty(PropertyMetaData property) throws Exception;

        void applyConventionMappingToGetter(PropertyMetaData property, Method getter) throws Exception;

        void applyConventionMappingToSetter(PropertyMetaData property, Method setter) throws Exception;

        void applyConventionMappingToSetMethod(PropertyMetaData property, Method metaMethod) throws Exception;

        void addSetMethod(PropertyMetaData propertyMetaData, Method setter) throws Exception;

        void addActionMethod(Method method) throws Exception;

        void addPropertySetters(PropertyMetaData property, Method getter) throws Exception;

        void generateServiceRegistrySupportMethods();

        Class<? extends T> generate() throws Exception;
    }
}
