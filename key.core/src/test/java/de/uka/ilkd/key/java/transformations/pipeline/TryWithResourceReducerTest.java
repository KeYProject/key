/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 *
 * @author Alexander Weigl
 * @version 1 (12.07.26)
 */
class TryWithResourceReducerTest {
    @Test
    void test() {
        String source = """
                class Demo {
                    void run() {
                        try (Resource r1 = new Resource1(); Resource r2 = new Resource2()) {
                            r1.use();
                            r2.use();
                        } catch (Exception e) {
                            System.out.println("caught: " + e);
                        } finally {
                            System.out.println("done");
                        }
                    }
                }
                """;

        CompilationUnit cu = StaticJavaParser.parse(source);
        var t = new TryWithResourceReducer();
        t.apply(cu);
        var actual = cu.toString();
        var expected = """
                class Demo {

                     void run() {
                         try {
                             Resource r1 = new Resource1();
                             Throwable primaryExc$1 = null;
                             try {
                                 Resource r2 = new Resource2();
                                 Throwable primaryExc$2 = null;
                                 try {
                                     r1.use();
                                     r2.use();
                                 } catch (Throwable t$2) {
                                     primaryExc$2 = t$2;
                                     throw t$2;
                                 } finally {
                                     if (r2 != null) {
                                         if (primaryExc$2 != null)
                                             try {
                                                 r2.close();
                                             } catch (Throwable suppressedExc$2) {
                                                 primaryExc$2.addSuppressed(suppressedExc$2);
                                             }
                                         else {
                                             r2.close();
                                         }
                                     }
                                 }
                             } catch (Throwable t$1) {
                                 primaryExc$1 = t$1;
                                 throw t$1;
                             } finally {
                                 if (r1 != null) {
                                     if (primaryExc$1 != null)
                                         try {
                                             r1.close();
                                         } catch (Throwable suppressedExc$1) {
                                             primaryExc$1.addSuppressed(suppressedExc$1);
                                         }
                                     else {
                                         r1.close();
                                     }
                                 }
                             }
                         } catch (Exception e) {
                             System.out.println("caught: " + e);
                         } finally {
                             System.out.println("done");
                         }
                     }
                 }
                """;

        assertThat(actual).isEqualToNormalizingWhitespace(expected);
    }

    @Test
    void testJava9() {
        String source = """
                class Demo {
                    Resource r1 = new Resource1();
                    void run() {
                        try (this.r1; Resource r2 = new Resource2()) {
                            r1.use();
                            r2.use();
                        } catch (Exception e) {
                            System.out.println("caught: " + e);
                        } finally {
                            System.out.println("done");
                        }
                    }
                }
                """;

        CompilationUnit cu = StaticJavaParser.parse(source);
        var t = new TryWithResourceReducer();
        t.apply(cu);
        var actual = cu.toString();


        var expected = """
                class Demo {
                     Resource r1 = new Resource1();
                     void run() {
                         try {
                             Throwable primaryExc$1 = null;
                             try {
                                 Resource r2 = new Resource2();
                                 Throwable primaryExc$2 = null;
                                 try {
                                     r1.use();
                                     r2.use();
                                 } catch (Throwable t$2) {
                                     primaryExc$2 = t$2;
                                     throw t$2;
                                 } finally {
                                     if (r2 != null) {
                                         if (primaryExc$2 != null)
                                             try {
                                                 r2.close();
                                             } catch (Throwable suppressedExc$2) {
                                                 primaryExc$2.addSuppressed(suppressedExc$2);
                                             }
                                         else {
                                             r2.close();
                                         }
                                     }
                                 }
                             } catch (Throwable t$1) {
                                 primaryExc$1 = t$1;
                                 throw t$1;
                             } finally {
                                 if (this.r1 != null) {
                                     if (primaryExc$1 != null)
                                         try {
                                             this.r1.close();
                                         } catch (Throwable suppressedExc$1) {
                                             primaryExc$1.addSuppressed(suppressedExc$1);
                                         }
                                     else {
                                         this.r1.close();
                                     }
                                 }
                             }
                         } catch (Exception e) {
                             System.out.println("caught: " + e);
                         } finally {
                             System.out.println("done");
                         }
                     }
                 }
                """;
        assertThat(actual).isEqualToNormalizingWhitespace(expected);
    }
}
