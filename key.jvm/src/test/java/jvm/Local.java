/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package jvm;

import java.util.ArrayList;
import java.util.List;

/**
 * Executable reference implementation of the {@code jvm.Local} stack machine, used only by the
 * M3 differential harness ({@code org.key_project.jvm.DifferentialTest}): a test-only twin of
 * the proof runtime shipped in {@code key.jvm/src/main/resources/.../runtime/jvm/Local.java},
 * whose Java bodies are empty (the transpiled code is proved, never executed — KeY applies the
 * JML contracts there, so bodies are irrelevant). This class gives the transpiled output
 * <em>real</em> behavior so it can be executed against the original bytecode on random inputs.
 * <p>
 * The semantics mirror the JML contracts of the proof runtime exactly: the stack is stored
 * <em>top-first</em> in a list (element 0 is the top), one logical element per JVM value
 * (a long/double/float occupies one entry; the two JVM slots only matter for
 * {@code LocalVariableTable} numbering, which the transpiler mirrors in plain-Java locals).
 * Only the operations the goto-free transpiled fixtures emit are exercised; the assembly is
 * therefore kept to that set and grows together with the fixtures.
 */
public class Local {

    /** The operand stack, top-first (element 0 is the top); {@code null} is a legal element. */
    private final List<Object> stack = new ArrayList<>();

    public Local() {
    }

    // -- int stack --------------------------------------------------------------------

    public void push(int v) {
        stack.add(0, v);
    }

    public int pop() {
        return (Integer) stack.remove(0);
    }

    public int top() {
        return (Integer) stack.get(0);
    }

    // -- reference stack -----------------------------------------------------------------

    public void push(Object v) {
        stack.add(0, v);
    }

    public Object popRef() {
        return stack.remove(0);
    }

    public Object topRef() {
        return stack.get(0);
    }

    // -- category-2: long/double/float (M3) -----------------------------------------------

    public void pushL(long v) {
        stack.add(0, v);
    }

    public long popL() {
        return (Long) stack.remove(0);
    }

    public long topL() {
        return (Long) stack.get(0);
    }

    public void pushD(double v) {
        stack.add(0, v);
    }

    public double popD() {
        return (Double) stack.remove(0);
    }

    public double topD() {
        return (Double) stack.get(0);
    }

    public void pushF(float v) {
        stack.add(0, v);
    }

    public float popF() {
        return (Float) stack.remove(0);
    }

    public float topF() {
        return (Float) stack.get(0);
    }

    // -- arithmetic (the subset the differential fixtures emit) ---------------------------

    /** int add: pops the two top ints, pushes their sum (JVM {@code iadd}). */
    public void iadd() {
        int b = pop();
        int a = pop();
        push(a + b);
    }

    /** long add: pops the two top longs, pushes their sum (JVM {@code ladd}). */
    public void ladd() {
        long b = popL();
        long a = popL();
        pushL(a + b);
    }

    /** double multiply (JVM {@code dmul}). */
    public void dmul() {
        double b = popD();
        double a = popD();
        pushD(a * b);
    }

    /** double add (JVM {@code dadd}). */
    public void dadd() {
        double b = popD();
        double a = popD();
        pushD(a + b);
    }

    /** float multiply (JVM {@code fmul}). */
    public void fmul() {
        float b = popF();
        float a = popF();
        pushF(a * b);
    }

    // -- comparisons / branches (surface only: never executed) -----------------------------

    /**
     * long compare, pushing {@code -1}/{@code 0}/{@code 1} (JVM {@code lcmp}). Faithful body;
     * the transpiled {@code lcmpish} also branches afterwards, so the method is excluded from
     * differential execution because of the {@code goto}.
     */
    public void lcmp() {
        long b = popL();
        long a = popL();
        push(Long.compare(a, b));
    }

    /** Pops the top int and reports whether it was {@code >= 0} (JVM {@code ifge}). */
    public boolean ifge() {
        return pop() >= 0;
    }

    /** Pops the top int and reports whether it was {@code == 0} (JVM {@code ifeq}). */
    public boolean ifeq() {
        return pop() == 0;
    }

    /**
     * Placeholder for the jump model of the {@code java-jvm} profile: the transpiler emits
     * {@code goto_(pc)} where the bytecode jumps, but Java cannot jump, so the semantics live
     * in the profile's {@code goto} rules applied by the theorem prover — not in this body.
     * Any transpiled method containing this call is therefore <em>excluded</em> from the
     * differential harness (it would silently fall through). Intentionally a no-op.
     */
    public static void goto_(int pc) {
    }

    // -- conversions (M3) -----------------------------------------------------------------

    /** int → long widening (JVM {@code i2l}). */
    public void i2l() {
        pushL((long) pop());
    }

    /** long → int truncation (JVM {@code l2i}). */
    public void l2i() {
        push((int) popL());
    }

    /** int → double widening (JVM {@code i2d}). */
    public void i2d() {
        pushD((double) pop());
    }

    // -- shuffles --------------------------------------------------------------------------

    /** Duplicates the top int/reference (JVM {@code dup}). */
    public void dup() {
        stack.add(0, stack.get(0));
    }

    /** Duplicates the top two values as a unit (JVM {@code dup2}). */
    public void dup2() {
        Object v1 = stack.remove(0);
        Object v2 = stack.remove(0);
        stack.add(0, v2);
        stack.add(0, v1);
        stack.add(0, v2);
        stack.add(0, v1);
    }
}
