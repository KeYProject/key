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
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LocalVariableNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.VarInsnNode;

/**
 * Transpiles a single method from bytecode into compilable Java source over the {@code jvm.Local}
 * runtime (M1, int subset).
 * <p>
 * The output is the <em>canonical linear layout</em>: parameters and JVM local variables become
 * <em>plain Java locals</em> (no {@code iload}/{@code istore}/{@code setLocal*} calls in the
 * output), and the JVM operand stack becomes one {@code jvm.Local} instance whose JML contracts
 * model the stack as a {@code \seq} ghost:
 * {@code stk.push(a);} ({@code iload}), {@code x = stk.pop();} ({@code istore}),
 * {@code stk.iadd();} (binary ops), {@code if (stk.if_icmplt()) { jvm.Local.goto_(pc); }}
 * (conditional jumps), {@code return stk.top();} ({@code ireturn}).
 * <p>
 * Every branch target {@code pc} becomes a Java label
 * {@code L<pc>: { if (false) { break L<pc>; } ... }} whose guard keeps KeY's {@code unusedLabel}
 * taclet away; forward/backward jumps become {@code jvm.Local.goto_(pc);}. Mid-layout
 * {@code return}/{@code ireturn} are wrapped in {@code if (true) { ... }} for javac reachability.
 * Unsupported instructions abort loudly.
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
    /** Fresh temporary variable counter for popped call arguments. */
    private int nextTemp = 0;

    private final StringBuilder body = new StringBuilder();
    /** JVM slots used for plain int local variables (parameters are excluded). */
    private final Set<Integer> localSlots = new TreeSet<>();
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
    }

    private static boolean isSlotOpcode(int opcode) {
        return switch (opcode) {
            case Opcodes.ILOAD, Opcodes.ISTORE, Opcodes.ALOAD, Opcodes.ASTORE -> true;
            default -> false;
        };
    }

    /** The JVM slots occupied by the (int) parameters. */
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
                "Method without bytecode code is not supported in M1: " + method.name);
        }
        pickStackVar();
        StringBuilder sb = new StringBuilder();
        sb.append("    ").append(modifier()).append(type()).append(method.name)
                .append(parameterList()).append(" {\n");
        sb.append(prologue());
        emit();
        sb.append(body).append("    }\n");
        return sb.toString();
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
        Integer[] params = paramSlots().toArray(new Integer[0]);
        for (int i = 0; i < params.length; i++) {
            if (params[i] == slot) {
                return paramName(i);
            }
        }
        return "local_" + slot;
    }

    private static String jvmTypeName(Type t) {
        if (t.getSort() == Type.ARRAY) {
            return jvmTypeName(t.getElementType()) + "[]".repeat(t.getDimensions());
        }
        if (t.getSort() == Type.OBJECT) {
            String internal = t.getInternalName();
            int slash = internal.lastIndexOf('/');
            return internal.substring(slash + 1);
        }
        // primitives
        return t.getClassName();
    }

    private String prologue() {
        StringBuilder sb = new StringBuilder();
        for (int slot : localSlots) {
            sb.append("        int ").append(localName(slot)).append(";\n");
        }
        sb.append("        jvm.Local ").append(stackVar).append(" = new jvm.Local();\n");
        return sb.toString();
    }

    private void emit() {
        int index = 0;
        boolean inLabeled = false;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn =
            insn.getNext(), index++) {
            if (targets.contains(index)) {
                if (inLabeled) {
                    line("        }");
                }
                line("        L" + index + ": { if (false) { break L" + index + "; }");
                inLabeled = true;
            }
            emitInstruction(insn, index);
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
            case Opcodes.ILOAD ->
                line("        " + stackVar + ".push(" + localName(((VarInsnNode) insn).var)
                    + ");");
            case Opcodes.ISTORE ->
                line("        " + localName(((VarInsnNode) insn).var) + " = " + stackVar
                    + ".pop();");
            case Opcodes.IINC -> {
                IincInsnNode inc = (IincInsnNode) insn;
                String name = localName(inc.var);
                line("        " + name + " = " + name + " + " + inc.incr + ";");
            }
            case Opcodes.GOTO ->
                line("        jvm.Local.goto_(" + targetOffset((JumpInsnNode) insn) + ");");
            case Opcodes.IF_ICMPEQ, Opcodes.IF_ICMPNE, Opcodes.IF_ICMPLT, Opcodes.IF_ICMPGE,
                    Opcodes.IF_ICMPGT, Opcodes.IF_ICMPLE -> {
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
            case Opcodes.IADD, Opcodes.ISUB, Opcodes.IMUL, Opcodes.IDIV, Opcodes.IREM, Opcodes.INEG,
                    Opcodes.IAND, Opcodes.IOR, Opcodes.IXOR, Opcodes.ISHL, Opcodes.ISHR,
                    Opcodes.IUSHR ->
                line("        " + stackVar + "." + mnemonic(op) + "();");
            case Opcodes.INVOKESTATIC -> emitStaticCall((MethodInsnNode) insn);
            case Opcodes.IRETURN ->
                line(index == lastOpcodeIndex ? "        return " + stackVar + ".top();"
                        : "        if (true) { return " + stackVar + ".top(); }");
            case Opcodes.RETURN ->
                line(index == lastOpcodeIndex ? "        return;"
                        : "        if (true) { return; }");
            case Opcodes.POP ->
                line("        " + stackVar + ".pop();");
            case Opcodes.DUP ->
                line("        " + stackVar + ".dup();");
            case Opcodes.SWAP ->
                line("        " + stackVar + ".swap();");
            case Opcodes.ACONST_NULL, Opcodes.ALOAD, Opcodes.ASTORE -> unsupported(insn);
            default -> unsupported(insn);
        }
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
        Type[] args = Type.getArgumentTypes(call.desc);
        if (ret.getSort() != Type.INT) {
            unsupported(call);
        }
        String[] temps = new String[args.length];
        for (int i = args.length - 1; i >= 0; i--) {
            if (args[i].getSort() != Type.INT) {
                unsupported(call);
            }
            temps[i] = "$v" + (nextTemp++);
            line("        int " + temps[i] + " = " + stackVar + ".pop();");
        }
        String target = className.equals(call.owner)
                ? call.name
                : call.owner.substring(call.owner.lastIndexOf('/') + 1) + "." + call.name;
        line("        " + stackVar + ".push(" + target + "(" + String.join(", ", temps) + "));");
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
            "Unsupported bytecode instruction in M1 (method " + method.name + "): "
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
