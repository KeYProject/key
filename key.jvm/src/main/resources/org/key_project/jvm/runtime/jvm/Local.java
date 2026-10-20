/* This file is part of the KeY/JVM runtime. It is copied verbatim by the transpiler into every
 * output folder so that the transpiled Java is self-contained and javac-checkable.
 *
 * SPDX-License-Identifier: GPL-2.0-or-later */
package jvm;

/**
 * Runtime model of the JVM operand stack for the M1 int subset: the stack contents live in two
 * <em>ghost fields</em>, a {@code \\seq} {@link #contents} and an {@code int} {@link #size}, i.e.
 * the stack is a first-order logic value (the "Sequence data type" of KeY's JML), not a heap
 * data structure.
 *
 * <p>The sequence is stored <em>top-first</em>: {@code contents[0]} is the top of the stack and
 * {@code contents[size-1]} the bottom. This keeps every operation length-free -- the NJML
 * translator of the loaded {@code \\javaSource} has no {@code \\seq_length}/{@code .length} form,
 * so the end index of {@code \\seq_sub} is taken from the {@link #size} ghost instead.
 *
 * <p>Every operation is a pure transition on the ghost fields stated by its JML contract (the
 * Java bodies are empty or return a dummy: the transpiled code is never executed, only proved,
 * and KeY's {@code methodExpansion: modularOnly} applies the contracts). The transpiler emits
 * the mnemonics as method calls on its single stack object, e.g. {@code iload 1} becomes
 * {@code stk.push(a);}, {@code istore 2} becomes {@code x = stk.pop();},
 * {@code if_icmplt L} becomes {@code if (stk.if_icmplt()) { jvm.Local.goto_(L); }} and
 * {@code ireturn} {@code return stk.top();}.
 *
 * <p>Because the stack is a {@code \\seq} ghost there are <em>no</em> heap fields, no fresh
 * objects, no array bounds and no NPE obligations: a proof over the transpiled method only ever
 * reasons about one {@code Local} instance (created up front by {@code new jvm.Local()}) and the
 * sequence formulas of the contracts. Local variables and method parameters are <em>not</em>
 * modeled here at all -- the transpiler emits them as plain Java locals.
 *
 * <p>Note on {@code goto_}: it intentionally has <em>no</em> contract and is {@code static}.
 * Transpiled jumps are handled by the {@code GotoSpliceRule}/{@code GotoRestoreRule} built-in
 * rules of the {@code java-jvm} profile (which match by method name), never by operation
 * contracts.
 *
 * <p>JVM arithmetic wraps like Java {@code int}s (no overflow checks), so proofs must run in
 * KeY's Java math mode ({@code intRules: javaSemantics}); the generated {@code .key} files set
 * this. Division, remainder, bitwise and shift operations have no contracts (KeY's first-order
 * int theory has no bitwise operators, and division needs an exceptional case); they are unused
 * by the M1 fixtures. M2 adds reference-typed stack operations ({@link #push(Object)},
 * {@link #popRef()}, {@link #topRef()}, reference comparisons/branches); the ghost
 * {@code \seq} holds {@code any}-sorted elements, so int and reference values share one stack;
 * M3 adds long/float/double (category-2): a long/double/float is one logical element per stack
 * entry (the two JVM slots a category-2 value occupies only number the {@code LocalVariableTable}
 * slots, which the transpiler mirrors in plain-Java locals), plus the JVM conversion mnemonics.
 */
public class Local {

    /**
     * The int operand stack of this frame, top-first (element 0 is the top). KeY's JML
     * translates {@code \\seq}, {@code \\seq_get}, {@code \\seq_concat} and {@code \\seq_sub}.
     * Note: KeY's {@code create} initializes a fresh object's {@code \\seq} ghost field to
     * {@code null} (not the empty sequence), so the {@link #Local() constructor contract}
     * restores {@code contents == \\seq_empty && size == 0} for every caller -- without it every
     * downstream sequence formula would fight a {@code null} sequence and the proof stalls.
     * NJML resolves {@code \\seq_get} to an {@code any}-sorted term, so every element use inside
     * an arithmetic comparison is cast ({@code (int)\\seq_get(...)}) -- the proofs then see
     * plain int {@code cast} terms.
     */
    //@ public instance ghost \seq contents;

    /** The number of elements on the stack; bounds every {@code \\seq_sub} end index. */
    //@ public instance ghost int size;

    /*@ public normal_behavior
      @   assignable contents, size;
      @   ensures contents == \seq_empty;
      @   ensures size == 0;
      @*/
    public Local() {
    }

    // -- stack effects ----------------------------------------------------------------

    /*@ public normal_behavior
      @   assignable contents, size;
      @   ensures size == \old(size) + 1;
      @   ensures contents == \seq_concat(\seq(v), \old(contents));
      @*/
    public void push(int v) {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == \seq_get(\old(contents), 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public int pop() {
        return 0;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   requires size > 0;
      @   ensures \result == \seq_get(contents, 0);
      @*/
    public int top() {
        return 0;
    }

    // -- reference-typed stack operations (M2) ------------------------------------------
    //
    // The ghost \seq stores any-sorted elements, so int and reference values share one stack;
    // well-typed bytecode never mixes them at one slot. push(new_obj)/push(field) widen to
    // push(Object); ASTORE/aread introduce the real Java cast ((T) stk.popRef()) whose
    // checkcast obligation KeY discharges from the static type.

    /*@ public normal_behavior
      @   assignable contents, size;
      @   ensures size == \old(size) + 1;
      @   ensures contents == \seq_concat(\seq(v), \old(contents));
      @*/
    public void push(Object v) {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == \seq_get(\old(contents), 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public Object popRef() {
        return null;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   requires size > 0;
      @   ensures \result == \seq_get(contents, 0);
      @*/
    public Object topRef() {
        return null;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == ((Object)\seq_get(\old(contents), 0) == null);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public boolean if_null() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == ((Object)\seq_get(\old(contents), 0) != null);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public boolean if_nonnull() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures \result ==
      @           ((Object)\seq_get(\old(contents), 1) == (Object)\seq_get(\old(contents), 0));
      @   ensures size == \old(size) - 2;
      @   ensures contents == \seq_sub(\old(contents), 2, \old(size));
      @*/
    public boolean if_acmpeq() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures \result ==
      @           ((Object)\seq_get(\old(contents), 1) != (Object)\seq_get(\old(contents), 0));
      @   ensures size == \old(size) - 2;
      @   ensures contents == \seq_sub(\old(contents), 2, \old(size));
      @*/
    public boolean if_acmpne() {
        return false;
    }

    // -- int arithmetic (value2 op value1 per the JVM spec; result pushed) ------------

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((int)\seq_get(\old(contents), 1)
      @                           + (int)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void iadd() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((int)\seq_get(\old(contents), 1)
      @                           - (int)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void isub() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((int)\seq_get(\old(contents), 1)
      @                           * (int)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void imul() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq(-(int)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void ineg() {
    }

    // -- long / float / double (category-2; the ghost \seq models one logical value per stack
    //    element, so lload/lstore/ladd treat a long as a single entry -- the two JVM slots a
    //    category-2 value occupies only matter for the LocalVariableTable slot numbering, which
    //    the transpiler mirrors in its plain-Java locals; javac never splits a category-2 value,
    //    so the element granularity is faithful) ----------------------------------------------

    /*@ public normal_behavior
      @   assignable contents, size;
      @   ensures size == \old(size) + 1;
      @   ensures contents == \seq_concat(\seq(v), \old(contents));
      @*/
    public void pushL(long v) {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == (long)\seq_get(\old(contents), 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public long popL() {
        return 0L;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   requires size > 0;
      @   ensures \result == (long)\seq_get(contents, 0);
      @*/
    public long topL() {
        return 0L;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   ensures size == \old(size) + 1;
      @   ensures contents == \seq_concat(\seq(v), \old(contents));
      @*/
    public void pushD(double v) {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == (double)\seq_get(\old(contents), 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public double popD() {
        return 0.0;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   requires size > 0;
      @   ensures \result == (double)\seq_get(contents, 0);
      @*/
    public double topD() {
        return 0.0;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   ensures size == \old(size) + 1;
      @   ensures contents == \seq_concat(\seq(v), \old(contents));
      @*/
    public void pushF(float v) {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == (float)\seq_get(\old(contents), 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public float popF() {
        return 0.0f;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   requires size > 0;
      @   ensures \result == (float)\seq_get(contents, 0);
      @*/
    public float topF() {
        return 0.0f;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((long)\seq_get(\old(contents), 1)
      @                           + (long)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void ladd() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((long)\seq_get(\old(contents), 1)
      @                           - (long)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void lsub() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((long)\seq_get(\old(contents), 1)
      @                           * (long)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void lmul() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq(-(long)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void lneg() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((double)\seq_get(\old(contents), 1)
      @                           + (double)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void dadd() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((double)\seq_get(\old(contents), 1)
      @                           - (double)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void dsub() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((double)\seq_get(\old(contents), 1)
      @                           * (double)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void dmul() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq(-(double)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void dneg() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((float)\seq_get(\old(contents), 1)
      @                           + (float)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void fadd() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((float)\seq_get(\old(contents), 1)
      @                           - (float)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void fsub() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((float)\seq_get(\old(contents), 1)
      @                           * (float)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void fmul() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq(-(float)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void fneg() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) - 1;
      @   ensures contents ==
      @           \seq_concat(\seq((long)\seq_get(\old(contents), 1)
      @                           > (long)\seq_get(\old(contents), 0) ? 1
      @                       : ((long)\seq_get(\old(contents), 1)
      @                           < (long)\seq_get(\old(contents), 0) ? -1 : 0)),
      @                       \seq_sub(\old(contents), 2, \old(size)));
      @*/
    public void lcmp() {
    }

    // -- conversions (replace the top stack element by its converted value) ---------------

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((long)(int)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void i2l() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((int)(long)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void l2i() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((float)(int)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void i2f() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((int)(float)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void f2i() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((double)(float)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void f2d() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((float)(double)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void d2f() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((double)(int)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void i2d() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((int)(double)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void d2i() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((float)(long)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void l2f() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((long)(float)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void f2l() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((double)(long)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void l2d() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((long)(double)\seq_get(\old(contents), 0)),
      @                       \seq_sub(\old(contents), 1, \old(size)));
      @*/
    public void d2l() {
    }

    // -- stack rearrangement ------------------------------------------------------------

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures size == \old(size) + 1;
      @   ensures contents ==
      @           \seq_concat(\seq((int)\seq_get(\old(contents), 0)), \old(contents));
      @*/
    public void dup() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size);
      @   ensures contents ==
      @           \seq_concat(\seq((int)\seq_get(\old(contents), 1)),
      @               \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @                           \seq_sub(\old(contents), 2, \old(size))));
      @*/
    public void swap() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) + 1;
      @   ensures contents ==
      @           \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @               \seq_concat(\seq((int)\seq_get(\old(contents), 1)),
      @                   \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @                               \seq_sub(\old(contents), 2, \old(size)))));
      @*/
    public void dup_x1() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 3;
      @   ensures size == \old(size) + 1;
      @   ensures contents ==
      @           \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @               \seq_concat(\seq((int)\seq_get(\old(contents), 2)),
      @                   \seq_concat(\seq((int)\seq_get(\old(contents), 1)),
      @                       \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @                                   \seq_sub(\old(contents), 3, \old(size))))));
      @*/
    public void dup_x2() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures size == \old(size) + 2;
      @   ensures contents ==
      @           \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @               \seq_concat(\seq((int)\seq_get(\old(contents), 1)),
      @                   \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @                       \seq_concat(\seq((int)\seq_get(\old(contents), 1)),
      @                                   \seq_sub(\old(contents), 2, \old(size))))));
      @*/
    public void dup2() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 3;
      @   ensures size == \old(size) + 2;
      @   ensures contents ==
      @           \seq_concat(\seq((int)\seq_get(\old(contents), 1)),
      @               \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @                   \seq_concat(\seq((int)\seq_get(\old(contents), 2)),
      @                       \seq_concat(\seq((int)\seq_get(\old(contents), 1)),
      @                           \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @                                       \seq_sub(\old(contents), 3, \old(size)))))));
      @*/
    public void dup2_x1() {
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 4;
      @   ensures size == \old(size) + 2;
      @   ensures contents ==
      @           \seq_concat(\seq((int)\seq_get(\old(contents), 1)),
      @               \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @                   \seq_concat(\seq((int)\seq_get(\old(contents), 3)),
      @                       \seq_concat(\seq((int)\seq_get(\old(contents), 2)),
      @                           \seq_concat(\seq((int)\seq_get(\old(contents), 1)),
      @                               \seq_concat(\seq((int)\seq_get(\old(contents), 0)),
      @                                           \seq_sub(\old(contents), 4, \old(size))))))));
      @*/
    public void dup2_x2() {
    }

    // -- branch predicates (pop their operands from the stack; value2 op value1) ---------

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures \result ==
      @           ((int)\seq_get(\old(contents), 1) < (int)\seq_get(\old(contents), 0));
      @   ensures size == \old(size) - 2;
      @   ensures contents == \seq_sub(\old(contents), 2, \old(size));
      @*/
    public boolean if_icmplt() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures \result ==
      @           ((int)\seq_get(\old(contents), 1) > (int)\seq_get(\old(contents), 0));
      @   ensures size == \old(size) - 2;
      @   ensures contents == \seq_sub(\old(contents), 2, \old(size));
      @*/
    public boolean if_icmpgt() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures \result ==
      @           ((int)\seq_get(\old(contents), 1) <= (int)\seq_get(\old(contents), 0));
      @   ensures size == \old(size) - 2;
      @   ensures contents == \seq_sub(\old(contents), 2, \old(size));
      @*/
    public boolean if_icmple() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures \result ==
      @           ((int)\seq_get(\old(contents), 1) >= (int)\seq_get(\old(contents), 0));
      @   ensures size == \old(size) - 2;
      @   ensures contents == \seq_sub(\old(contents), 2, \old(size));
      @*/
    public boolean if_icmpge() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures \result ==
      @           ((int)\seq_get(\old(contents), 1) == (int)\seq_get(\old(contents), 0));
      @   ensures size == \old(size) - 2;
      @   ensures contents == \seq_sub(\old(contents), 2, \old(size));
      @*/
    public boolean if_icmpeq() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size >= 2;
      @   ensures \result ==
      @           ((int)\seq_get(\old(contents), 1) != (int)\seq_get(\old(contents), 0));
      @   ensures size == \old(size) - 2;
      @   ensures contents == \seq_sub(\old(contents), 2, \old(size));
      @*/
    public boolean if_icmpne() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == ((int)\seq_get(\old(contents), 0) == 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public boolean ifeq() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == ((int)\seq_get(\old(contents), 0) != 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public boolean ifne() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == ((int)\seq_get(\old(contents), 0) < 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public boolean iflt() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == ((int)\seq_get(\old(contents), 0) >= 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public boolean ifge() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == ((int)\seq_get(\old(contents), 0) > 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public boolean ifgt() {
        return false;
    }

    /*@ public normal_behavior
      @   assignable contents, size;
      @   requires size > 0;
      @   ensures \result == ((int)\seq_get(\old(contents), 0) <= 0);
      @   ensures size == \old(size) - 1;
      @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
      @*/
    public boolean ifle() {
        return false;
    }

    // -- contractless stubs (unused by the M1 fixtures; KeY expands their empty bodies if it
    //    ever meets them, so proofs must not rely on them) --------------------------------

    public void idiv() {
    }

    public void irem() {
    }

    public void iand() {
    }

    public void ior() {
    }

    public void ixor() {
    }

    public void ishl() {
    }

    public void ishr() {
    }

    public void iushr() {
    }

    // category-2 counterparts of the contractless int stubs (division needs an exceptional
    // case, the float/double comparison mnemonics differ only in their NaN convention, which
    // KeY's float theory does not expose in JML; none of the long/float/double fixtures use
    // them, so they are emitted for round-trip completeness and never relied on in proofs)
    public void ldiv() {
    }

    public void lrem() {
    }

    public void ddiv() {
    }

    public void drem() {
    }

    public void fdiv() {
    }

    public void frem() {
    }

    public void dcmpg() {
    }

    public void dcmpl() {
    }

    public void fcmpg() {
    }

    public void fcmpl() {
    }

    // -- jumps ------------------------------------------------------------------------

    /**
     * Deliberately has no JML contract <em>and no Java body</em> ({@code native}): jumps are the
     * concern of GotoSpliceRule and GotoRestoreRule, not of operation contracts, and an empty
     * body must not silently become a no-op — under {@code methodExpansion} the strategy would
     * inline such a body, modeling a backward {@code goto_} as falling through (unsound: the
     * proof could then "close" with the jump dropped). Native keeps the expansion inapplicable,
     * so a {@code goto_} that neither rule resolves leaves the goal loudly stuck instead. The
     * target is a constant int bytecode offset (string literals are abbreviated by KeY's
     * symbolic engine, int constants survive). It is static: the transpiler emits
     * {@code jvm.Local.goto_(pc);} and the operand stack is untouched. The test-only executable
     * twin {@code src/test/java/jvm/Local.java} keeps a real Java body for the differential
     * harness; methods containing {@code goto_} there are excluded from execution anyway.
     */
    public static native void goto_(int pc);
}
