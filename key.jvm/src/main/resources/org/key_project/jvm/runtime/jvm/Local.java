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
 * {@code \seq} holds {@code any}-sorted elements, so int and reference values share one stack.
 * Long/float/double (category-2) stacks and arrays are M2/M3 follow-ups.
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

    // -- jumps ------------------------------------------------------------------------

    /**
     * Deliberately has no JML contract: jumps are the concern of GotoSpliceRule and
     * GotoRestoreRule, not of operation contracts. The target is a constant int bytecode offset
     * (string literals are abbreviated by KeY's symbolic engine, int constants survive). It is
     * static: the transpiler emits {@code jvm.Local.goto_(pc);} and the operand stack is
     * untouched.
     */
    public static void goto_(int pc) {
    }
}
