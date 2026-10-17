/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.transpiler;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LocalVariableNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;

/**
 * Transpiles a single method from bytecode into compilable Java source over the {@code jvm.Local}
 * runtime (M1 int subset + M2 references/fields/calls).
 * <p>
 * The output is the <em>canonical linear layout</em>: parameters and JVM local variables become
 * <em>plain Java locals</em> (no {@code iload}/{@code istore}/{@code setLocal*} calls in the
 * output), and the JVM operand stack becomes one {@code jvm.Local} instance whose JML contracts
 * model the stack as a {@code \seq} ghost:
 * {@code stk.push(a);} ({@code iload}/{@code aload}), {@code x = stk.pop();} /
 * {@code x = (T) stk.popRef();} ({@code istore}/{@code astore}),
 * {@code stk.iadd();} (binary ops), {@code if (stk.if_icmplt()) { jvm.Local.goto_(pc); }}
 * (conditional jumps), {@code return stk.top();} ({@code ireturn}/{@code areturn}).
 * <p>
 * Every branch target {@code pc} becomes a Java label
 * {@code L<pc>: { if (false) { break L<pc>; } ... }} whose guard keeps KeY's {@code unusedLabel}
 * taclet away; forward/backward jumps become {@code jvm.Local.goto_(pc);}. Mid-layout
 * {@code return} is wrapped in {@code if (true) { ... }} for javac reachability.
 * Unsupported instructions abort loudly.
 * <p>
 * Object model (M2): {@code new}+{@code dup}+{@code invokespecial <init>} is fused into
 * {@code T $tN = new T(args); stk.push($tN);} (the real allocation is a Java expression, the
 * stack only carries a reference), fields are real Java field accesses around
 * {@code popRef}/{@code push}, and instance calls are {@code stk.push($o.method(args))}. The
 * reference type of every JVM local slot comes from the {@code LocalVariableTable} (fixtures are
 * compiled with {@code -g}); a reference slot without debug type aborts loudly.
 */
public final class MethodTranspiler {

    private final MethodNode method;
    private final boolean isStatic;
    /** Internal name of the enclosing class (for self-referential calls). */
    private final String className;

    private final int instructionCount;
    /** Bytecode offsets (among all nodes, incl. line numbers) of jump targets. */
    private final Map<LabelNode, Integer> labelIndex = new HashMap<>();
    private final Set<Integer> targets = new HashSet<>();
    private int lastOpcodeIndex = -1;
    /** Fresh temporary variable counter for popped arguments/receivers/allocation temps. */
    private int nextTemp = 0;

    private final StringBuilder body = new StringBuilder();
    /** JVM slots used for plain Java local variables (parameters and {@code this} excluded). */
    private final Set<Integer> localSlots = new TreeSet<>();
    /**
     * Java type name of each JVM local slot (paremeters, {@code this}, and locals from the
     * {@code LocalVariableTable}).
     */
    private final Map<Integer, String> slotTypes = new HashMap<>();
    /** The name of the runtime operand-stack variable in the emitted method. */
    private String stackVar = "stk";

    public MethodTranspiler(MethodNode method, boolean isStatic, String className) {
        this.method = method;
        this.isStatic = isStatic;
        this.className = className;
        // first pass: instruction offsets and all jump targets
        int off = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn =
            insn.getNext(), off++) {
            if (insn instanceof LabelNode labelNode) {
                labelIndex.put(labelNode, off);
            }
        }
        instructionCount = off;
        int nodeIdx = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn =
            insn.getNext(), nodeIdx++) {
            if (insn instanceof JumpInsnNode jump) {
                targets.add(labelIndex.get(jump.label));
            }
            if (insn.getOpcode() != -1) {
                lastOpcodeIndex = nodeIdx;
            }
            if (insn instanceof VarInsnNode var && isSlotOpcode(var.getOpcode())) {
                localSlots.add(var.var);
            }
            if (insn instanceof IincInsnNode iinc) {
                localSlots.add(iinc.var);
            }
        }
        localSlots.removeAll(paramSlots());
        if (!isStatic) {
            // `this` lives in slot 0 of instance methods; it is implicit, never declared.
            localSlots.remove(0);
        }
        indexSlotTypes();
    }

    private static boolean isSlotOpcode(int opcode) {
        return switch (opcode) {
            case Opcodes.ILOAD, Opcodes.ISTORE, Opcodes.ALOAD, Opcodes.ASTORE -> true;
            default -> false;
        };
    }

    /**
     * Registers the Java type of every local slot: {@code this}, parameters, then the
     * {@code LocalVariableTable} (fixtures compiled with {@code -g}).
     */
    private void indexSlotTypes() {
        if (!isStatic) {
            slotTypes.put(0, jvmTypeName(Type.getObjectType(className)));
        }
        Type[] args = Type.getArgumentTypes(method.desc);
        int slot = isStatic ? 0 : 1;
        for (Type arg : args) {
            slotTypes.put(slot, jvmTypeName(arg));
            slot += arg.getSize();
        }
        if (method.localVariables != null) {
            for (LocalVariableNode lv : method.localVariables) {
                slotTypes.putIfAbsent(lv.index, jvmTypeName(Type.getType(lv.desc)));
            }
        }
    }

    /** The JVM slots occupied by the parameters. */
    private Set<Integer> paramSlots() {
        Set<Integer> slots = new TreeSet<>();
        Type[] args = Type.getArgumentTypes(method.desc);
        int slot = isStatic ? 0 : 1;
        for (Type arg : args) {
            slots.add(slot);
            slot += arg.getSize();
        }
        return slots;
    }

    /** @return the complete Java method source (signature prologue + body). */
    public String transpile() {
        if (instructionCount == 0) {
            throw new UnsupportedOperationException(
                "Method without bytecode code is not supported in M1/M2: " + method.name);
        }
        pickStackVar();
        StringBuilder sb = new StringBuilder();
        sb.append("    ").append(modifier()).append(methodHeader()).append(" {\n");
        sb.append(prologue());
        emit();
        sb.append(body).append("    }\n");
        return sb.toString();
    }

    private String methodHeader() {
        if (method.name.equals("<init>")) {
            return simpleName(className) + parameterList();
        }
        String retType = type();
        return retType + method.name + parameterList();
    }

    /** Avoids a name clash between the runtime stack variable and a source-level parameter. */
    private void pickStackVar() {
        Set<String> used = new HashSet<>();
        Type[] args = Type.getArgumentTypes(method.desc);
        for (int i = 0; i < args.length; i++) {
            used.add(paramName(i));
        }
        while (used.contains(stackVar)) {
            stackVar = "_" + stackVar;
        }
    }

    private String modifier() {
        return java.lang.reflect.Modifier.isStatic(method.access) ? "public static " : "public ";
    }

    private String type() {
        Type t = Type.getReturnType(method.desc);
        if (t.getSort() == Type.VOID) {
            return "void";
        }
        return jvmTypeName(t) + " ";
    }

    private String parameterList() {
        Type[] args = Type.getArgumentTypes(method.desc);
        if (args.length == 0) {
            return "()";
        }
        StringBuilder sb = new StringBuilder("(");
        for (int i = 0; i < args.length; i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(jvmTypeName(args[i])).append(' ').append(paramName(i));
        }
        return sb.append(')').toString();
    }

    /** Best-effort parameter names from LocalVariableTable; falls back to {@code a<pos>}. */
    private String paramName(int position) {
        int slot = paramSlots().toArray(new Integer[0])[position];
        if (method.localVariables != null) {
            for (LocalVariableNode lv : method.localVariables) {
                if (lv.index == slot && !lv.name.equals("this")) {
                    return lv.name;
                }
            }
        }
        return "a" + position;
    }

    /** The Java name of the plain local variable holding JVM local slot {@code slot}. */
    private String localName(int slot) {
        if (slot == 0 && !isStatic) {
            return "this";
        }
        Integer[] params = paramSlots().toArray(new Integer[0]);
        for (int i = 0; i < params.length; i++) {
            if (params[i] == slot) {
                return paramName(i);
            }
        }
        return "local_" + slot;
    }

    /** The Java type name of JVM local slot {@code slot} (defaults to {@code int}). */
    private String slotType(int slot) {
        return slotTypes.getOrDefault(slot, "int");
    }

    /** JVM type descriptor → Java source type (arrays as {@code T[]}, objects as simple name). */
    public static String jvmTypeName(Type t) {
        if (t.getSort() == Type.ARRAY) {
            return jvmTypeName(t.getElementType()) + "[]".repeat(t.getDimensions());
        }
        if (t.getSort() == Type.OBJECT) {
            return simpleName(t.getInternalName());
        }
        // primitives
        return t.getClassName();
    }

    private static String simpleName(String internalName) {
        int slash = internalName.lastIndexOf('/');
        return slash < 0 ? internalName : internalName.substring(slash + 1);
    }

    private String prologue() {
        StringBuilder sb = new StringBuilder();
        for (int slot : localSlots) {
            String t = slotType(slot);
            if (t.equals("long") || t.equals("double")) {
                throw new UnsupportedOperationException(
                    "Category-2 local in method " + method.name + " is not supported in M2");
            }
            sb.append("        ").append(t).append(' ').append(localName(slot)).append(";\n");
        }
        sb.append("        jvm.Local ").append(stackVar).append(" = new jvm.Local();\n");
        return sb.toString();
    }

    private void emit() {
        int index = 0;
        boolean inLabeled = false;
        String pendingNew = null;
        boolean skippedDup = false;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn =
            insn.getNext(), index++) {
            if (targets.contains(index)) {
                if (pendingNew != null) {
                    throw new UnsupportedOperationException(
                        "Jump target inside a new+<init> pattern in method " + method.name);
                }
                if (inLabeled) {
                    line("        }");
                }
                line("        L" + index + ": { if (false) { break L" + index + "; }");
                inLabeled = true;
            }
            if (insn.getOpcode() == Opcodes.NEW) {
                if (pendingNew != null) {
                    throw new UnsupportedOperationException(
                        "Nested allocation in " + method.name + " is not supported in M2");
                }
                pendingNew = ((TypeInsnNode) insn).desc;
                skippedDup = false;
                continue; // no push: the fused <init> emits the object
            }
            if (insn.getOpcode() == Opcodes.DUP && pendingNew != null && !skippedDup) {
                skippedDup = true;
                continue; // the pattern's dup: consumed by the fusion
            }
            if (insn instanceof MethodInsnNode call && pendingNew != null
                    && call.name.equals("<init>") && call.owner.equals(pendingNew)) {
                emitAllocation(call);
                pendingNew = null;
                continue;
            }
            if (pendingNew != null) {
                // instructions between dup and <init> must be pure argument pushes
                if (!isConstructorArgumentPush(insn)) {
                    throw new UnsupportedOperationException(
                        "Unsupported instruction inside new+<init> pattern in method "
                            + method.name + ": " + mnemonic(insn.getOpcode()));
                }
            }
            emitInstruction(insn, index);
        }
        if (pendingNew != null) {
            throw new UnsupportedOperationException(
                "new without matching <init> in method " + method.name);
        }
        if (inLabeled) {
            line("        }");
            // A labeled statement containing a reachable `break <label>` (the transpiler's guard)
            // "completes normally" for javac's reachability analysis, so a non-void method ending
            // inside such a block would otherwise report "missing return statement". Append a dead
            // `return <zero>;`. The guard is never taken (constant false), so KeY never reaches it.
            line("        return " + zeroValue(Type.getReturnType(method.desc).getSort()) + ";");
        }
    }

    /** Instructions that may appear inside a new+<init> pattern: argument pushes only. */
    private static boolean isConstructorArgumentPush(AbstractInsnNode insn) {
        return switch (insn.getOpcode()) {
            case Opcodes.ILOAD, Opcodes.ALOAD, Opcodes.LDC, Opcodes.ICONST_M1, Opcodes.ICONST_0,
                    Opcodes.ICONST_1, Opcodes.ICONST_2, Opcodes.ICONST_3, Opcodes.ICONST_4,
                    Opcodes.ICONST_5, Opcodes.BIPUSH, Opcodes.SIPUSH, Opcodes.ACONST_NULL,
                    Opcodes.GETFIELD, Opcodes.GETSTATIC, Opcodes.INVOKEVIRTUAL,
                    Opcodes.INVOKESPECIAL,
                    Opcodes.INVOKEINTERFACE, Opcodes.INVOKESTATIC ->
                true;
            default -> false;
        };
    }

    /** A dead return value for a method whose body ends inside a guard-labeled block. */
    private static String zeroValue(int sort) {
        return switch (sort) {
            case Type.BOOLEAN -> "false";
            case Type.CHAR -> "'\\u0000'";
            case Type.BYTE, Type.SHORT, Type.INT -> "0";
            case Type.LONG -> "0L";
            case Type.FLOAT -> "0.0f";
            case Type.DOUBLE -> "0.0";
            case Type.ARRAY, Type.OBJECT -> "null";
            default -> throw new UnsupportedOperationException("Unsupported return type " + sort);
        };
    }

    private void emitInstruction(AbstractInsnNode insn, int index) {
        if (insn.getOpcode() == -1) {
            return; // LabelNode, LineNumberNode, FrameNode
        }
        final int op = insn.getOpcode();
        switch (op) {
            case Opcodes.NOP -> {
            } // no-op
            case Opcodes.ICONST_M1 -> pushLiteral(-1);
            case Opcodes.ICONST_0 -> pushLiteral(0);
            case Opcodes.ICONST_1 -> pushLiteral(1);
            case Opcodes.ICONST_2 -> pushLiteral(2);
            case Opcodes.ICONST_3 -> pushLiteral(3);
            case Opcodes.ICONST_4 -> pushLiteral(4);
            case Opcodes.ICONST_5 -> pushLiteral(5);
            case Opcodes.BIPUSH, Opcodes.SIPUSH -> {
                int operand = ((IntInsnNode) insn).operand;
                if (operand < -32768) {
                    unsupported(insn);
                }
                pushLiteral(operand);
            }
            case Opcodes.LDC -> {
                Object cst = ((LdcInsnNode) insn).cst;
                if (cst instanceof Integer v) {
                    pushLiteral(v);
                } else {
                    unsupported(insn);
                }
            }
            case Opcodes.ILOAD, Opcodes.ALOAD ->
                line("        " + stackVar + ".push(" + localName(((VarInsnNode) insn).var)
                    + ");");
            case Opcodes.ISTORE ->
                line("        " + localName(((VarInsnNode) insn).var) + " = " + stackVar
                    + ".pop();");
            case Opcodes.ASTORE -> {
                int slot = ((VarInsnNode) insn).var;
                String t = slotType(slot);
                if (t.equals("int")) {
                    throw new UnsupportedOperationException(
                        "Reference store to an int-typed slot " + slot + " in " + method.name);
                }
                line("        " + localName(slot) + " = (" + t + ") " + stackVar + ".popRef();");
            }
            case Opcodes.IINC -> {
                IincInsnNode inc = (IincInsnNode) insn;
                String name = localName(inc.var);
                line("        " + name + " = " + name + " + " + inc.incr + ";");
            }
            case Opcodes.GOTO ->
                line("        jvm.Local.goto_(" + targetOffset((JumpInsnNode) insn) + ");");
            case Opcodes.IF_ICMPEQ, Opcodes.IF_ICMPNE, Opcodes.IF_ICMPLT, Opcodes.IF_ICMPGE,
                    Opcodes.IF_ICMPGT, Opcodes.IF_ICMPLE, Opcodes.IF_ACMPEQ, Opcodes.IF_ACMPNE -> {
                int target = targetOffset((JumpInsnNode) insn);
                line("        if (" + stackVar + "." + mnemonic(op) + "()) { "
                    + "jvm.Local.goto_(" + target + "); }");
            }
            case Opcodes.IFEQ, Opcodes.IFNE, Opcodes.IFLT, Opcodes.IFGE, Opcodes.IFGT,
                    Opcodes.IFLE -> {
                int target = targetOffset((JumpInsnNode) insn);
                line("        if (" + stackVar + "." + mnemonic(op) + "()) { "
                    + "jvm.Local.goto_(" + target + "); }");
            }
            case Opcodes.IFNULL, Opcodes.IFNONNULL -> {
                int target = targetOffset((JumpInsnNode) insn);
                String predicate = op == Opcodes.IFNULL ? "if_null" : "if_nonnull";
                line("        if (" + stackVar + "." + predicate + "()) { "
                    + "jvm.Local.goto_(" + target + "); }");
            }
            case Opcodes.IADD, Opcodes.ISUB, Opcodes.IMUL, Opcodes.IDIV, Opcodes.IREM, Opcodes.INEG,
                    Opcodes.IAND, Opcodes.IOR, Opcodes.IXOR, Opcodes.ISHL, Opcodes.ISHR,
                    Opcodes.IUSHR ->
                line("        " + stackVar + "." + mnemonic(op) + "();");
            case Opcodes.INVOKESTATIC -> emitStaticCall((MethodInsnNode) insn);
            case Opcodes.INVOKEVIRTUAL, Opcodes.INVOKESPECIAL, Opcodes.INVOKEINTERFACE -> {
                MethodInsnNode call = (MethodInsnNode) insn;
                if (call.name.equals("<init>")) {
                    // not consumed by the new+<init> fusion: an explicit super(...) call
                    handleSuperInit(call);
                } else {
                    emitInstanceCall(call);
                }
            }
            case Opcodes.GETFIELD -> emitGetField((FieldInsnNode) insn);
            case Opcodes.PUTFIELD -> emitPutField((FieldInsnNode) insn);
            case Opcodes.IRETURN ->
                line("        " + returnStatement(index, "return " + stackVar + ".top();"));
            case Opcodes.ARETURN ->
                line("        " + returnStatement(index,
                    "return (" + jvmTypeName(Type.getReturnType(method.desc)) + ") " + stackVar
                        + ".topRef();"));
            case Opcodes.RETURN ->
                line("        " + returnStatement(index, "return;"));
            case Opcodes.ACONST_NULL ->
                line("        " + stackVar + ".push((Object) null);");
            case Opcodes.POP ->
                line("        " + stackVar + ".pop();");
            case Opcodes.DUP ->
                line("        " + stackVar + ".dup();");
            case Opcodes.SWAP ->
                line("        " + stackVar + ".swap();");
            default -> unsupported(insn);
        }
    }

    /** Wraps a mid-layout return statement for javac reachability (JLS 14.22). */
    private String returnStatement(int index, String statement) {
        return index == lastOpcodeIndex ? statement : "if (true) { " + statement + " }";
    }

    private void pushLiteral(int value) {
        line("        " + stackVar + ".push(" + value + ");");
    }

    /**
     * Emits a static call whose int arguments are popped off the operand stack (top first, i.e.
     * reverse declaration order) and whose int result is pushed back on it. Only int-typed
     * arguments/return are supported in M1; any other shape aborts loudly.
     */
    private void emitStaticCall(MethodInsnNode call) {
        Type ret = Type.getReturnType(call.desc);
        if (ret.getSort() != Type.INT) {
            unsupportedCall(call);
        }
        String[] temps = popArguments(call, "$v");
        String target = className.equals(call.owner)
                ? call.name
                : simpleName(call.owner) + "." + call.name;
        line("        " + stackVar + ".push(" + target + "(" + String.join(", ", temps) + "));");
    }

    /** Pops the method's arguments (top first, i.e. reverse declaration order) into typed temps. */
    private String[] popArguments(MethodInsnNode call, String prefix) {
        Type[] args = Type.getArgumentTypes(call.desc);
        String[] temps = new String[args.length];
        for (int i = args.length - 1; i >= 0; i--) {
            temps[i] = freshTemp(prefix);
            line("        " + declaredTemp(args[i], temps[i]) + ";");
        }
        return temps;
    }

    /** Pops the receiver of an instance call off the stack. */
    private String popReceiver(MethodInsnNode call) {
        String recv = freshTemp("$o");
        line("        " + jvmTypeName(Type.getObjectType(call.owner)) + " " + recv + " = ("
            + jvmTypeName(Type.getObjectType(call.owner)) + ") " + stackVar + ".popRef();");
        return recv;
    }

    /**
     * Emits an instance call (invokevirtual/invokespecial-non-init/invokeinterface): pops
     * receiver and arguments off the operand stack (top first), calls the method on the receiver
     * (a real Java expression) and pushes a non-void result back on the stack.
     */
    private void emitInstanceCall(MethodInsnNode call) {
        String[] args = popArguments(call, "$a");
        String recv = popReceiver(call);
        String invocation = recv + "." + call.name + "(" + String.join(", ", args) + ")";
        if (Type.getReturnType(call.desc).getSort() == Type.VOID) {
            line("        " + invocation + ";");
        } else {
            line("        " + stackVar + ".push(" + invocation + ");");
        }
    }

    /**
     * A constructor invocation left over from the fusion: an explicit {@code super(...)} call in
     * a transpiled {@code <init>}. The Java compiler inserts {@code super()} implicitly, so the
     * canonical {@code super()} of {@code java.lang.Object} is dropped (its receiver, {@code this},
     * is popped). Any other super-call (e.g. {@code super(x, y)} of a non-Object superclass) is
     * M2-unsupported: the emitted constructor starts with the runtime frame, so Java's
     * "super must be the first statement" rule cannot be satisfied.
     */
    private void handleSuperInit(MethodInsnNode call) {
        if (call.owner.equals("java/lang/Object")
                && Type.getArgumentTypes(call.desc).length == 0) {
            line("        " + stackVar + ".popRef();");
            return;
        }
        unsupportedCall(call);
    }

    /** getfield: pops the receiver and pushes the field value (depth unchanged). */
    private void emitGetField(FieldInsnNode field) {
        String recv = freshTemp("$o");
        String owner = jvmTypeName(Type.getObjectType(field.owner));
        line("        " + owner + " " + recv + " = (" + owner + ") " + stackVar + ".popRef();");
        line("        " + stackVar + ".push(" + recv + "." + field.name + ");");
    }

    /** putfield: pops the value (on top), then the receiver, and assigns the real field. */
    private void emitPutField(FieldInsnNode field) {
        String value = freshTemp("$v");
        line("        " + declaredTemp(Type.getType(field.desc), value) + ";");
        String recv = freshTemp("$o");
        String owner = jvmTypeName(Type.getObjectType(field.owner));
        line("        " + owner + " " + recv + " = (" + owner + ") " + stackVar + ".popRef();");
        line("        " + recv + "." + field.name + " = " + value + ";");
    }

    /**
     * The {@code new T}; {@code dup}; {@code <args>}; {@code invokespecial T.<init>} fusion: the
     * argument temps were already popped (reverse order) while emitting... no -- the argument
     * pushes were emitted before this point, so pop them off the stack now, then emit the real
     * allocation {@code T $tN = new T(args); stk.push($tN);}. The stack depth must be one higher
     * afterwards (the single copy of the initialized reference), exactly like the JVM.
     */
    private void emitAllocation(MethodInsnNode init) {
        String[] args = popArguments(init, "$c");
        String obj = freshTemp("$t");
        String owner = jvmTypeName(Type.getObjectType(init.owner));
        line("        " + owner + " " + obj + " = new " + owner + "("
            + String.join(", ", args) + ");");
        line("        " + stackVar + ".push(" + obj + ");");
    }

    /**
     * Declaration of a temp for a JVM descriptor: int sorts via {@code pop}, refs via
     * {@code popRef} with the real Java cast (checkcast obligation from the static type).
     */
    private String declaredTemp(Type type, String name) {
        String t = jvmTypeName(type);
        switch (type.getSort()) {
            case Type.BOOLEAN, Type.BYTE, Type.CHAR, Type.SHORT, Type.INT -> {
                return "int " + name + " = " + stackVar + ".pop()";
            }
            case Type.LONG, Type.FLOAT, Type.DOUBLE ->
                throw new UnsupportedOperationException(
                    "Category-2 argument/return in method " + method.name + " is not supported");
            case Type.OBJECT, Type.ARRAY -> {
                return t + " " + name + " = (" + t + ") " + stackVar + ".popRef()";
            }
            default -> throw new UnsupportedOperationException(
                "Unsupported type sort " + type.getSort());
        }
    }

    private String freshTemp(String prefix) {
        return prefix + (nextTemp++);
    }

    private void unsupportedCall(MethodInsnNode call) {
        throw new UnsupportedOperationException(
            "Unsupported method call shape in " + method.name + ": " + call.owner + "." + call.name
                + call.desc);
    }

    private int targetOffset(JumpInsnNode jump) {
        Integer idx = labelIndex.get(jump.label);
        if (idx == null) {
            throw new IllegalStateException("jump to unknown label in " + method.name);
        }
        return idx;
    }

    private void unsupported(AbstractInsnNode insn) {
        throw new UnsupportedOperationException(
            "Unsupported bytecode instruction in " + method.name + ": "
                + mnemonic(insn.getOpcode()));
    }

    private void line(String text) {
        body.append(text).append('\n');
    }

    private static String mnemonic(int opcode) {
        for (var field : Opcodes.class.getFields()) {
            try {
                if (((int) field.get(null)) == opcode) {
                    return field.getName().toLowerCase();
                }
            } catch (IllegalAccessException ignored) {
                // keep scanning
            }
        }
        return "opc_" + opcode;
    }
}
