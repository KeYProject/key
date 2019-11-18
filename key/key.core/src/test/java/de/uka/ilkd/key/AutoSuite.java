package de.uka.ilkd.key;

import junit.framework.TestCase;
import org.junit.Test;
import org.junit.experimental.categories.Category;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.RunnerBuilder;

import java.io.File;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;

public class AutoSuite extends Suite {

    /** System property that can be set to true if debug output is needed. */
    private static final boolean DEBUG_OUTPUT =
            Boolean.getBoolean("key.test.autosuite.debug");

    /** test categories to be excluded */
    private static List excludedCategories = Collections.emptyList();

    /** test classes to be excluded */
    private static List excludedClasses = Collections.emptyList();

    /** comparator for ascending lexicographic ordering */
    private static final Comparator<? super Class<?>> LEXICOGRAPHIC_ASC
        = Comparator.comparing(Class::getName);

    @Retention(RetentionPolicy.RUNTIME)      // ensures that annotation is available via reflection
    @Target({ElementType.TYPE})
    public @interface AutoSuitePath {
        /** @return the path of the AutoSuite */
        String value();
    }

    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.TYPE})
    @interface AutoSuiteExclude {
        /** @return the categories to exclude completely */
        Class[] categories() default {};
        /** @return the classes that are excluded explicitly */
        Class[] classes() default {};
    }

    /**
     * Called reflectively on classes annotated with <code>@RunWith(AutoSuite.class)</code>
     *
     * @param klass the root class
     * @param builder builds runners for classes in the suite
     * @throws InitializationError if initialization fails
     */
    public AutoSuite(Class<?> klass, RunnerBuilder builder) throws InitializationError {
        super(builder, klass, findTestClasses(klass));
    }

    private static Class<?>[] findTestClasses(Class<?> klass) throws InitializationError {

        AutoSuitePath suitePath = klass.getAnnotation(AutoSuitePath.class);
        if (suitePath == null) {
            throw new InitializationError("Root class is not annotated with AutoSuitePath: "
                + klass);
        }

        parseExclusions(klass);

        String path = suitePath.value();

        List<Class<?>> result = findTestClasses(new File(path), "");

        // remove the suite class itself from the suite ...
        // if it happens to be included.
        result.remove(klass);

        result.sort(LEXICOGRAPHIC_ASC);

        debug("AutoTestSuite: ");
        for (Class<?> c : result) {
            debug("    " + c.getName());
        }

        return result.toArray(new Class[0]);
    }

    /**
     * Go and look for a {@link AutoSuiteExclude} annotation and store its values (if present)
     * into the files
     *
     * @param klass The @AutoSuite annotated test suite class
     */
    private static void parseExclusions(Class<?> klass) {
        AutoSuiteExclude exclude = klass.getAnnotation(AutoSuiteExclude.class);
        if (exclude != null) {
            excludedCategories = Arrays.asList(exclude.categories());
            excludedClasses = Arrays.asList(exclude.classes());
        }
    }

    private static List<Class<?>> findTestClasses(File file, final String packagePrefix)
        throws InitializationError {

        List<Class<?>> result = new ArrayList<>();
        if (file.isDirectory()) {
            File[] files = file.listFiles();
            if (files != null) {
                for (File f : files) {
                    String prefix = packagePrefix;
                    if (f.isDirectory()) {
                        prefix += (packagePrefix.isEmpty() ? "" : ".") + f.getName();
                    }
                    result.addAll(findTestClasses(f, prefix));
                }
            }
        } else {
            if (file.getName().endsWith(".class")) {
                findClass(file.getName(), packagePrefix).ifPresent(result::add);
            }
        }

        return result;
    }

    private static Optional<Class<?>> findClass(String fileName, final String packagePrefix)
        throws InitializationError {
        // extract actual class name
        int end = fileName.lastIndexOf('.');
        int start = fileName.lastIndexOf('.', end - 1);
        String className = fileName.substring(start + 1, end);

        // ignore inner and anonymous classes
        if (className.contains("$")) {
            return Optional.empty();
        }

        String qualifiedClassName = packagePrefix
                                  + (packagePrefix.isEmpty() ? "" : ".")
                                  + className;
        try {
            debug("Searching for class " + qualifiedClassName);

            // initialization of ProofJavaParser fails somehow (why?)
            // -> disable initialization of classes
            Class<?> clss =
                Class.forName(qualifiedClassName, false, AutoSuite.class.getClassLoader());

            if (excludedClasses.contains(clss)) {
                // This class has been excluded explicitly!
                return Optional.empty();
            }

            if (Modifier.isAbstract(clss.getModifiers())) {
                // An abstract class is not a test class
                return Optional.empty();
            }

            if (!isTestClass(clss)) {
                return Optional.empty();
            }

            Category category = clss.getAnnotation(Category.class);
            if (category != null) {
                Class[] categories = category.value();
                for (Class c : categories) {
                    // completely exclude specific categories
                    if (excludedCategories.contains(c)) {
                        return Optional.empty();
                    }
                }
            }

            return Optional.of(clss);

        } catch (ClassNotFoundException e) {
            throw new InitializationError(e);
        }
    }

    /**
     * See also https://docs.gradle.org/current/userguide/java_testing.html#sec:test_detection
     * <p>
     * For JUnit, Gradle scans for both JUnit 3 and 4 test classes. A class is considered to
     * be a JUnit test if it:
     * <ol><li> Ultimately inherits from TestCase or GroovyTestCase
     * <li> Is annotated with @RunWith
     * <li> Contains a method annotated with @Test or a super class does
     * </ol>
     *
     * @param clss the class to check
     * @return true iff the given class is considered to be a JUnit test
     */
    private static boolean isTestClass(Class<?> clss) {
        // Instances of TestClass are also test classes.
        if(TestCase.class.isAssignableFrom(clss)) {
            debug("    found (is legacy test class)!");
            return true;
        }

        // include class if it is a test suite
        RunWith annotation = clss.getAnnotation(RunWith.class);
        if (annotation != null) {
            if(annotation.value() == AutoSuite.class) {
                // We do not want to nest auto suites! Hence
                // any auto suite is not considered a test case for us.
                // Hence, one can keep several auto suites in one directory
                // w/o that they include each other
                return false;
            }
            debug("    found (is test suite)!");
            // return here to prevent double inclusion of suite classes with test methods
            return true;
        }

        // include class if it contains test methods:
        // iterate methods and check for @Test.class
        for (Method m : clss.getDeclaredMethods()) {
            debug("    method " + m.getName());
            if (m.getAnnotation(Test.class) != null) {
                debug("    found (contains test method)!");
                return true;
            }
        }

        // the class is considered to be a test if it is subclass of a test class
        Class<?> superClass = clss.getSuperclass();
        if (superClass != null) {
            return isTestClass(superClass);
        }

        return false;
    }

    private static void debug(String msg) {
        if (DEBUG_OUTPUT) {
            System.err.println(msg);
        }
    }
}
