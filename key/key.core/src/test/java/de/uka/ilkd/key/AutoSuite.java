package de.uka.ilkd.key;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.RunnerBuilder;

import java.io.File;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;

public class AutoSuite extends Suite {

    /** comparator for ascending lexicographic ordering */
    private static final Comparator<? super Class<?>> LEXICOGRAPHIC_ASC
        = Comparator.comparing(Class::getName);

    @Retention(RetentionPolicy.RUNTIME)      // ensures that annotation is available via reflection
    @interface AutoSuitePath {
        /** @return the path of the AutoSuite */
        String value();
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

        // TODO NPE and others
        String path = klass.getAnnotation(AutoSuitePath.class).value();

        List<Class<?>> result = findTestClasses(new File(path), "");
        result.sort(LEXICOGRAPHIC_ASC);

        System.out.println("AutoTestSuite: ");
        for (Class<?> c : result) {
            System.out.println("    " + c.getName());
        }

        return result.toArray(new Class[0]);
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
            } else {
                throw new InitializationError("Error! The given path does not denote" +
                    "a directory: " + file);
            }
        } else {
            if(file.getName().endsWith(".class")) {
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

        // prevent TestCore test suite from containing itself
        if (className.equals("TestCore")) {
            return Optional.empty();
        }

        String qualifiedClassName = packagePrefix
                                  + (packagePrefix.isEmpty() ? "" : ".")
                                  + className;
        try {
            System.out.println("Searching for class " + qualifiedClassName);

            // initialization of ProofJavaParser fails somehow (why?)
            // -> disable initialization of classes
            Class<?> clss =
                Class.forName(qualifiedClassName, false, AutoSuite.class.getClassLoader());

            // TODO: should we manually filter for test category here?

            // include class if it is a test suite
            if (clss.getAnnotation(RunWith.class) != null) {
                System.out.println("found (is test suite)!");
                // return here to prevent double inclusion of suite classes with test methods
                return Optional.of(clss);
            }

            // include class if it contains test methods
            // iterate methods and check for @Test.class
            for (Method m : clss.getDeclaredMethods()) {
                System.out.println("    method " + m.getName());
                if (m.getAnnotation(Test.class) != null) {
                    System.out.println("found (contains test method)!");
                    return Optional.of(clss);        // already found a test -> we can skip the rest
                }
            }
        } catch (ClassNotFoundException e) {
            throw new InitializationError(e);
        }
        return Optional.empty();
    }
}
