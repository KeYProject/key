/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the {@link MultiCatchReducer} transformer.
 *
 * @author Alexander Weigl
 * @version 1 (12.07.26)
 */
class MultiCatchReducerTest {
    @Test
    void testSimpleMultiCatch() {
        String source = """
                class Demo {
                    void run() {
                        try {
                            doSomething();
                        } catch (Exception1 | Exception2 e) {
                            System.out.println("caught: " + e);
                        }
                    }
                    void doSomething() throws Exception1, Exception2 {}
                }
                """;

        CompilationUnit cu = StaticJavaParser.parse(source);
        var t = new MultiCatchReducer();
        t.apply(cu);
        var actual = cu.toString();

        var expected = """
                class Demo {

                    void run() {
                        try {
                            doSomething();
                        } catch (final Exception1 e) {
                            System.out.println("caught: " + e);
                        } catch (final Exception2 e) {
                            System.out.println("caught: " + e);
                        }
                    }

                    void doSomething() throws Exception1, Exception2 {
                    }
                }
                """;

        assertThat(actual).isEqualToNormalizingWhitespace(expected);
    }

    @Test
    void testThreeExceptionTypes() {
        String source = """
                class Demo {
                    void run() {
                        try {
                            doSomething();
                        } catch (IOException | SQLException | RuntimeException e) {
                            handle(e);
                        }
                    }
                    void doSomething() throws IOException, SQLException, RuntimeException {}
                    void handle(Exception e) {}
                }
                """;

        CompilationUnit cu = StaticJavaParser.parse(source);
        var t = new MultiCatchReducer();
        t.apply(cu);
        var actual = cu.toString();

        var expected = """
                class Demo {

                    void run() {
                        try {
                            doSomething();
                        } catch (final IOException e) {
                            handle(e);
                        } catch (final SQLException e) {
                            handle(e);
                        } catch (final RuntimeException e) {
                            handle(e);
                        }
                    }

                    void doSomething() throws IOException, SQLException, RuntimeException {
                    }

                    void handle(Exception e) {
                    }
                }
                """;

        assertThat(actual).isEqualToNormalizingWhitespace(expected);
    }

    @Test
    void testMixedSingleAndMultiCatch() {
        String source = """
                class Demo {
                    void run() {
                        try {
                            doSomething();
                        } catch (IllegalArgumentException e) {
                            log("illegal arg");
                        } catch (IOException | SQLException e) {
                            log("io/sql error");
                        } catch (RuntimeException e) {
                            throw e;
                        }
                    }
                    void doSomething() throws IOException, SQLException {}
                    void log(String s) {}
                }
                """;

        CompilationUnit cu = StaticJavaParser.parse(source);
        var t = new MultiCatchReducer();
        t.apply(cu);
        var actual = cu.toString();

        var expected = """
                class Demo {

                    void run() {
                        try {
                            doSomething();
                        } catch (IllegalArgumentException e) {
                            log("illegal arg");
                        } catch (final IOException e) {
                            log("io/sql error");
                        } catch (final SQLException e) {
                            log("io/sql error");
                        } catch (RuntimeException e) {
                            throw e;
                        }
                    }

                    void doSomething() throws IOException, SQLException {
                    }

                    void log(String s) {
                    }
                }
                """;

        assertThat(actual).isEqualToNormalizingWhitespace(expected);
    }

    @Test
    void testMultiCatchWithFinally() {
        String source = """
                class Demo {
                    void run() {
                        try {
                            doSomething();
                        } catch (Exception1 | Exception2 e) {
                            handle(e);
                        } finally {
                            cleanup();
                        }
                    }
                    void doSomething() throws Exception1, Exception2 {}
                    void handle(Exception e) {}
                    void cleanup() {}
                }
                """;

        CompilationUnit cu = StaticJavaParser.parse(source);
        var t = new MultiCatchReducer();
        t.apply(cu);
        var actual = cu.toString();

        var expected = """
                class Demo {

                    void run() {
                        try {
                            doSomething();
                        } catch (final Exception1 e) {
                            handle(e);
                        } catch (final Exception2 e) {
                            handle(e);
                        } finally {
                            cleanup();
                        }
                    }

                    void doSomething() throws Exception1, Exception2 {
                    }

                    void handle(Exception e) {
                    }

                    void cleanup() {
                    }
                }
                """;

        assertThat(actual).isEqualToNormalizingWhitespace(expected);
    }

    @Test
    void testNoMultiCatchUnchanged() {
        String source = """
                class Demo {
                    void run() {
                        try {
                            doSomething();
                        } catch (Exception e) {
                            handle(e);
                        }
                    }
                    void doSomething() throws Exception {}
                    void handle(Exception e) {}
                }
                """;

        CompilationUnit cu = StaticJavaParser.parse(source);
        var original = cu.toString();
        var t = new MultiCatchReducer();
        t.apply(cu);
        var actual = cu.toString();

        // Should remain unchanged since there's no multi-catch
        assertThat(actual).isEqualToNormalizingWhitespace(original);
    }

    @Test
    void testMultiMultiCatch() {
        String source = """
                class Demo {
                    int f() {
                        try { m(); }
                        catch (IllegalArgumentException | NullPointerException e) { return 1; }
                        catch (ArithmeticException | ArrayStoreException e)       { return 2; }
                        return 0;
                    }
                }
                """;

        CompilationUnit cu = StaticJavaParser.parse(source);
        var original = cu.toString();
        var t = new MultiCatchReducer();
        t.apply(cu);
        var actual = cu.toString();

        // Should remain unchanged since there's no multi-catch
        assertThat(actual).isEqualToNormalizingWhitespace("""
                class Demo {
                    int f() {
                        try {
                            m();
                        } catch (final IllegalArgumentException e) {
                            return 1;
                        } catch (final NullPointerException e) {
                            return 1;
                        } catch (final ArithmeticException e) {
                            return 2;
                        } catch (final ArrayStoreException e) {
                            return 2;
                        }
                        return 0;
                    }
                }
                """);
    }
}
