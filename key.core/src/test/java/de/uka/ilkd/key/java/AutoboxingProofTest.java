/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * End-to-end proofs for boxing and unboxing in assignment contexts.
 */
class AutoboxingProofTest {

    @BeforeAll
    static void enableJml() {
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                .setActiveStrategyProperties(new StrategyProperties());
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
    }

    private static Proof proof(String className, String source, String method, Path dir)
            throws Exception {
        return proof(className, source, method, dir, false);
    }

    private static Proof proof(String className, String source, String method, Path dir,
            boolean expandLoops) throws Exception {
        Path sub = Files.createDirectories(dir.resolve(className));
        Path file = sub.resolve(className + ".java");
        Files.writeString(file, source);

        KeYEnvironment<?> env = KeYEnvironment.load(file);
        try {
            var contract = env.getProofContracts().stream()
                    .filter(c -> c.getTarget() instanceof IProgramMethod pm
                            && pm.getMethodDeclaration().getName().equals(method))
                    .findFirst()
                    .orElseThrow(() -> new AssertionError("no contract for " + method));
            Proof proof = env.createProof(contract.createProofObl(env.getInitConfig()));
            if (expandLoops) {
                var properties =
                    proof.getSettings().getStrategySettings().getActiveStrategyProperties();
                properties.setProperty(StrategyProperties.LOOP_OPTIONS_KEY,
                    StrategyProperties.LOOP_SCOPE_EXPAND);
                proof.setActiveStrategy(
                    proof.getActiveStrategyFactory().create(proof, properties));
            }
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            return proof;
        } finally {
            env.dispose();
        }
    }

    private static void prove(String className, String source, Path dir) throws Exception {
        prove(className, source, dir, false);
    }

    private static void prove(String className, String source, Path dir, boolean expandLoops)
            throws Exception {
        Proof proof = proof(className, source, "m", dir, expandLoops);
        assertTrue(proof.closed(), () -> "Proof did not close. Open goals: " + proof.openGoals());
    }

    private static String clazz(String className, String body) {
        return """
                public class %s {
                    %s
                }
                """.formatted(className, body);
    }

    @Test
    void localVariable(@TempDir Path dir) throws Exception {
        prove("LocalVariable", clazz("LocalVariable", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 42;
                    int i = a;
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void fieldAssignment(@TempDir Path dir) throws Exception {
        prove("FieldAssignment", clazz("FieldAssignment", """
                Integer f;

                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public void m() {
                    f = 42;
                    int i = f;
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void returnValue(@TempDir Path dir) throws Exception {
        prove("ReturnValue", clazz("ReturnValue", """
                static Integer box() {
                    return 42;
                }

                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    int i = box();
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void boxesMethodArgument(@TempDir Path dir) throws Exception {
        prove("ArgumentBoxing", clazz("ArgumentBoxing", """
                static int id(Integer x) {
                    return x;
                }

                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    int i = id(42);
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void unboxesMethodArgument(@TempDir Path dir) throws Exception {
        prove("ArgumentUnboxing", clazz("ArgumentUnboxing", """
                static int id(int x) {
                    return x;
                }

                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 42;
                    int i = id(a);
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void boxesVarargsElements(@TempDir Path dir) throws Exception {
        prove("VarargsBoxing", clazz("VarargsBoxing", """
                static int first(Integer... xs) {
                    return xs[0];
                }

                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    int i = first(42);
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void arithmeticPromotion(@TempDir Path dir) throws Exception {
        prove("ArithmeticPromotion", clazz("ArithmeticPromotion", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 42;
                    int i = a + 1;
                    //@ assert i == 43;
                }
                """), dir);
    }

    @Test
    void mixedLongPromotion(@TempDir Path dir) throws Exception {
        prove("MixedLongPromotion", clazz("MixedLongPromotion", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 42;
                    long v = a + 1L;
                    //@ assert v == 43L;
                }
                """), dir);
    }

    @Test
    void booleanCondition(@TempDir Path dir) throws Exception {
        prove("BooleanCondition", clazz("BooleanCondition", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Boolean z = true;
                    int i = 0;
                    if (z) {
                        i = 1;
                    }
                    //@ assert i == 1;
                }
                """), dir);
    }

    @Test
    void arrayIndex(@TempDir Path dir) throws Exception {
        prove("ArrayIndex", clazz("ArrayIndex", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer idx = 1;
                    int[] values = new int[] { 5, 6, 7 };
                    int x = values[idx];
                    //@ assert x == 6;
                }
                """), dir);
    }

    @Test
    void switchSelector(@TempDir Path dir) throws Exception {
        prove("SwitchSelector", clazz("SwitchSelector", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 2;
                    int r = 0;
                    switch (a) {
                        case 1: r = 1; break;
                        case 2: r = 2; break;
                        default: r = 0; break;
                    }
                    //@ assert r == 2;
                }
                """), dir);
    }

    @Test
    void compoundAssignment(@TempDir Path dir) throws Exception {
        prove("CompoundAssignment", clazz("CompoundAssignment", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 42;
                    a += 1;
                    int i = a;
                    //@ assert i == 43;
                }
                """), dir);
    }

    @Test
    void postIncrement(@TempDir Path dir) throws Exception {
        prove("PostIncrement", clazz("PostIncrement", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 42;
                    int i = a++;
                    int j = a;
                    //@ assert i == 42;
                    //@ assert j == 43;
                }
                """), dir);
    }

    @Test
    void preIncrement(@TempDir Path dir) throws Exception {
        prove("PreIncrement", clazz("PreIncrement", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 42;
                    int i = ++a;
                    //@ assert i == 43;
                }
                """), dir);
    }

    @Test
    void incrementInBinaryExpression(@TempDir Path dir) throws Exception {
        prove("IncrementBinary", clazz("IncrementBinary", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 42;
                    int i = a++ + a++;
                    int j = a;
                    //@ assert i == 85;
                    //@ assert j == 44;
                }
                """), dir);
    }

    @Test
    void incrementInCall(@TempDir Path dir) throws Exception {
        prove("IncrementCall", clazz("IncrementCall", """
                static int id(int x) {
                    return x;
                }

                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = 42;
                    int i = id(a++);
                    int j = a;
                    //@ assert i == 42;
                    //@ assert j == 43;
                }
                """), dir);
    }

    @Test
    void castBoxing(@TempDir Path dir) throws Exception {
        prove("CastBoxing", clazz("CastBoxing", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = (Integer) 42;
                    int i = a;
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void castUnboxing(@TempDir Path dir) throws Exception {
        prove("CastUnboxing", clazz("CastUnboxing", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = Integer.valueOf(42);
                    int i = (int) a;
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void castToObject(@TempDir Path dir) throws Exception {
        prove("CastToObject", clazz("CastToObject", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Object o = (Object) 42;
                    //@ assert o != null;
                }
                """), dir);
    }

    @Test
    void assignmentToNumber(@TempDir Path dir) throws Exception {
        prove("AssignmentToNumber", clazz("AssignmentToNumber", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Number n = 42;
                    //@ assert n != null;
                }
                """), dir);
    }

    @Test
    void numericConditional(@TempDir Path dir) throws Exception {
        prove("NumericConditional", clazz("NumericConditional", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = Integer.valueOf(42);
                    boolean f = true;
                    int i = f ? a : 0;
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void conditionalBoxing(@TempDir Path dir) throws Exception {
        prove("ConditionalBoxing", clazz("ConditionalBoxing", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    boolean f = false;
                    Integer a = f ? 1 : Integer.valueOf(42);
                    int i = a;
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void arrayInitializer(@TempDir Path dir) throws Exception {
        prove("ArrayInitializer", clazz("ArrayInitializer", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer[] xs = { 1, 2 };
                    int i = xs[1];
                    //@ assert i == 2;
                }
                """), dir);
    }

    @Test
    void arrayStoreAndRead(@TempDir Path dir) throws Exception {
        prove("ArrayStoreAndRead", clazz("ArrayStoreAndRead", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer[] xs = new Integer[2];
                    xs[0] = 42;
                    int i = xs[0];
                    //@ assert i == 42;
                }
                """), dir);
    }

    @Test
    void primitiveArrayStoreFromBoxed(@TempDir Path dir) throws Exception {
        prove("PrimitiveArrayStore", clazz("PrimitiveArrayStore", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    int[] a = new int[1];
                    Integer x = 42;
                    a[0] = x;
                    //@ assert a[0] == 42;
                }
                """), dir);
    }

    @Test
    void enhancedForBoxing(@TempDir Path dir) throws Exception {
        prove("EnhancedForBoxing", clazz("EnhancedForBoxing", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    int[] a = { 1, 2, 3 };
                    int s = 0;
                    for (Integer x : a) {
                        s += x;
                    }
                    //@ assert s == 6;
                }
                """), dir, true);
    }

    @Test
    void enhancedForUnboxing(@TempDir Path dir) throws Exception {
        prove("EnhancedForUnboxing", clazz("EnhancedForUnboxing", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer[] a = { 1, 2, 3 };
                    int s = 0;
                    for (int x : a) {
                        s += x;
                    }
                    //@ assert s == 6;
                }
                """), dir, true);
    }

    private record WrapperCase(String name, String primitive, String wrapper, String literal,
            String assignmentAssertion, String argumentAssertion) {
    }

    private static final java.util.List<WrapperCase> WRAPPERS = java.util.List.of(
        new WrapperCase("Boolean", "boolean", "Boolean", "true", "i", "j"),
        new WrapperCase("Byte", "byte", "Byte", "(byte) 42", "i == 42", "j == 42"),
        new WrapperCase("Short", "short", "Short", "(short) 42", "i == 42", "j == 42"),
        new WrapperCase("Character", "char", "Character", "'x'", "i == 'x'", "j == 'x'"),
        new WrapperCase("Integer", "int", "Integer", "42", "i == 42", "j == 42"),
        new WrapperCase("Long", "long", "Long", "42L", "i == 42L", "j == 42L"),
        new WrapperCase("Float", "float", "Float", "1.5f", "a != null", "b != null"),
        new WrapperCase("Double", "double", "Double", "1.5d", "a != null", "b != null"));

    @Test
    void allWrapperTypes(@TempDir Path dir) throws Exception {
        for (WrapperCase c : WRAPPERS) {
            String source = clazz(c.name() + "Assignment", """
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static void m() {
                        %s a = %s;
                        %s i = a;
                        //@ assert %s;
                    }
                    """.formatted(c.wrapper(), c.literal(), c.primitive(),
                c.assignmentAssertion()));
            prove(c.name() + "Assignment", source, dir);
        }
    }

    @Test
    void allWrapperArguments(@TempDir Path dir) throws Exception {
        for (WrapperCase c : WRAPPERS) {
            String source = clazz(c.name() + "Arguments", """
                    static %s id(%s x) {
                        return x;
                    }

                    static %s wid(%s x) {
                        return x;
                    }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static void m() {
                        %s i = id(%s.valueOf(%s));
                        %s b = wid(%s);
                        %s j = b;
                        //@ assert %s;
                    }
                    """.formatted(c.primitive(), c.primitive(), c.wrapper(), c.wrapper(),
                c.primitive(), c.wrapper(), c.literal(), c.wrapper(), c.literal(), c.primitive(),
                c.argumentAssertion()));
            prove(c.name() + "Arguments", source, dir);
        }
    }

    @Test
    void bothBoxedConditionalKeepsReferenceIdentity(@TempDir Path dir) throws Exception {
        prove("BothBoxedConditional", clazz("BothBoxedConditional", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = Integer.valueOf(1);
                    Integer b = Integer.valueOf(42);
                    boolean f = false;
                    Integer c = f ? a : b;
                    //@ assert c == b;
                }
                """), dir);
    }

    @Test
    void unboxesBothBoxedConditionalToPrimitive(@TempDir Path dir) throws Exception {
        prove("BothBoxedToPrimitive", clazz("BothBoxedToPrimitive", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = Integer.valueOf(1);
                    Integer b = Integer.valueOf(2);
                    boolean f = true;
                    int i = f ? a : b;
                    //@ assert i == 1;
                }
                """), dir);
    }

    @Test
    void bothBoxedConditionalSelectsNull(@TempDir Path dir) throws Exception {
        prove("NullConditionalBranch", clazz("NullConditionalBranch", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = null;
                    Integer b = Integer.valueOf(42);
                    boolean f = true;
                    Integer c = f ? a : b;
                    //@ assert c == null;
                }
                """), dir);
    }

    @Test
    void bothBoxedBooleanConditionalKeepsReferenceIdentity(@TempDir Path dir) throws Exception {
        prove("BoxedBooleanConditional", clazz("BoxedBooleanConditional", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Boolean a = Boolean.valueOf(true);
                    Boolean b = Boolean.valueOf(false);
                    boolean f = false;
                    Boolean c = f ? a : b;
                    //@ assert c == b;
                }
                """), dir);
    }

    @Test
    void boxesBooleanConditionalBranch(@TempDir Path dir) throws Exception {
        prove("BooleanConditionalBranch", clazz("BooleanConditionalBranch", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Boolean a = Boolean.valueOf(true);
                    boolean f = true;
                    Boolean c = f ? a : false;
                    boolean r = c;
                    //@ assert r;
                }
                """), dir);
    }

    @Test
    void booleanOperandsOfAnd(@TempDir Path dir) throws Exception {
        prove("BooleanAnd", clazz("BooleanAnd", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Boolean b = Boolean.valueOf(true);
                    boolean c = true;
                    boolean r = b & c;
                    //@ assert r;
                }
                """), dir);
    }

    @Test
    void booleanEqualityWithPrimitive(@TempDir Path dir) throws Exception {
        prove("BooleanEquality", clazz("BooleanEquality", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Boolean b = Boolean.valueOf(true);
                    boolean r = b == true;
                    //@ assert r;
                }
                """), dir);
    }

    @Test
    void booleanCompoundAssignment(@TempDir Path dir) throws Exception {
        prove("BooleanCompound", clazz("BooleanCompound", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Boolean b = Boolean.valueOf(true);
                    b &= true;
                    boolean r = b;
                    //@ assert r;
                }
                """), dir);
    }

    @Test
    void boxesNarrowedConstants(@TempDir Path dir) throws Exception {
        prove("NarrowedConstants", clazz("NarrowedConstants", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Character c = 65;
                    char ch = c;
                    //@ assert ch == 65;
                    Byte b = (short) 1;
                    byte bb = b;
                    //@ assert bb == 1;
                    Short s = (byte) 2;
                    short ss = s;
                    //@ assert ss == 2;
                }
                """), dir);
    }

    @Test
    void narrowsCompoundAssignmentAndConstantExpression(@TempDir Path dir) throws Exception {
        prove("ByteCompound", clazz("ByteCompound", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Byte b = 1 + 2;
                    byte x = b;
                    //@ assert x == 3;
                    b += 1;
                    byte y = b;
                    //@ assert y == 4;
                }
                """), dir);
    }

    @Test
    void nullUnboxingSplits(@TempDir Path dir) throws Exception {
        Proof proof = proof("NullUnboxing", clazz("NullUnboxing", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer a = null;
                    int i = a;
                }
                """), "m", dir);
        assertFalse(proof.closed(), "null unboxing must not silently verify");
        boolean falseGoal = proof.openGoals().stream().anyMatch(goal -> {
            String label = goal.node().getNodeInfo().getBranchLabel();
            boolean nullLabel = label != null && label.contains("Null");
            return nullLabel || goal.sequent().succedent().isEmpty();
        });
        assertTrue(falseGoal, () -> "expected the null/false branch, got: " + proof.openGoals());
    }

    @Test
    void charConditional(@TempDir Path dir) throws Exception {
        prove("CharConditional", clazz("CharConditional", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    char x = 'a';
                    char y = 'b';
                    boolean f = true;
                    char c = f ? x : y;
                    //@ assert c == 'a';
                }
                """), dir);
    }

    @Test
    void boxedByteAndShortConditional(@TempDir Path dir) throws Exception {
        prove("ByteShortConditional", clazz("ByteShortConditional", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Byte x = Byte.valueOf((byte) 1);
                    Short y = Short.valueOf((short) 2);
                    boolean f = true;
                    short s = f ? x : y;
                    //@ assert s == 1;
                }
                """), dir);
    }

    @Test
    void boxedIntegerAndLongConditional(@TempDir Path dir) throws Exception {
        prove("IntegerLongConditional", clazz("IntegerLongConditional", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    Integer x = Integer.valueOf(1);
                    Long y = Long.valueOf(2L);
                    boolean f = false;
                    long v = f ? x : y;
                    //@ assert v == 2L;
                }
                """), dir);
    }

    @Test
    void constantNarrowingConditional(@TempDir Path dir) throws Exception {
        prove("ConstantNarrowingConditional", clazz("ConstantNarrowingConditional", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    byte b = 2;
                    boolean f = true;
                    byte narrowed = f ? b : 2;
                    //@ assert narrowed == 2;
                    char c = f ? 'A' : 65;
                    //@ assert c == 65;
                }
                """), dir);
    }

    @Test
    void nullConditionalInOperator(@TempDir Path dir) throws Exception {
        prove("NullConditionalOperator", clazz("NullConditionalOperator", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    boolean f = false;
                    int i = (f ? null : 1) + 1;
                    //@ assert i == 2;
                }
                """), dir);
    }

    @Test
    void nullBooleanConditionalInOperator(@TempDir Path dir) throws Exception {
        prove("NullBooleanConditionalOperator", clazz("NullBooleanConditionalOperator", """
                /*@ normal_behavior
                  @ requires true;
                  @ ensures true;
                  @*/
                public static void m() {
                    boolean f = false;
                    Boolean b = (f ? null : true) & false;
                    boolean r = b;
                    //@ assert !r;
                }
                """), dir);
    }

    @Test
    void nullConditionalInOperatorSplits(@TempDir Path dir) throws Exception {
        Proof proof =
            proof("NullConditionalOperatorSplit", clazz("NullConditionalOperatorSplit", """
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static void m() {
                        boolean f = true;
                        int i = (f ? null : 1) + 1;
                    }
                    """), "m", dir);
        assertFalse(proof.closed(), "the null branch of the conditional must split");
        boolean falseGoal = proof.openGoals().stream().anyMatch(goal -> {
            String label = goal.node().getNodeInfo().getBranchLabel();
            boolean nullLabel = label != null && label.contains("Null");
            return nullLabel || goal.sequent().succedent().isEmpty();
        });
        assertTrue(falseGoal, () -> "expected the null/false branch, got: " + proof.openGoals());
    }
}
