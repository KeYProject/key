/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.transpiler;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
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
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
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
    /** Every node (labels, line numbers, frames and real instructions) by index. */
    private final List<AbstractInsnNode> nodes = new ArrayList<>();
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

    /**
     * Exception regions recovered from the exception table (M3): one entry per {@code try}
     * range, in javac's source order; {@code handlers} lists the catch clauses (table order, a
     * {@code null} type is the catch-all used by synchronized/finally inlining).
     */
    private final List<Region> tryRegions = new ArrayList<>();

    /** Indexes of the handler instructions, emitted inside the catch clauses, not linearly. */
    private final Set<Integer> consumed = new HashSet<>();

    public MethodTranspiler(MethodNode method, boolean isStatic, String className) {
        this.method = method;
        this.isStatic = isStatic;
        this.className = className;
        // first pass: instruction offsets and all jump targets
        int off = 0;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn =
            insn.getNext(), off++) {
            nodes.add(insn);
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
            if (insn instanceof TableSwitchInsnNode ts) {
                targets.add(labelIndex.get(ts.dflt));
                for (LabelNode label : ts.labels) {
                    targets.add(labelIndex.get(label));
                }
            }
            if (insn instanceof LookupSwitchInsnNode ls) {
                targets.add(labelIndex.get(ls.dflt));
                for (LabelNode label : ls.labels) {
                    targets.add(labelIndex.get(label));
                }
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
        analyzeTryCatch();
    }

    private static boolean isSlotOpcode(int opcode) {
        return switch (opcode) {
            case Opcodes.ILOAD, Opcodes.ISTORE, Opcodes.ALOAD, Opcodes.ASTORE, Opcodes.LLOAD,
                    Opcodes.LSTORE, Opcodes.DLOAD, Opcodes.DSTORE, Opcodes.FLOAD,
                    Opcodes.FSTORE ->
                true;
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
        sb.append("    ").append(modifier()).append(methodHeader()).append(throwsClause())
                .append(" {\n");
        sb.append(prologue());
        emit();
        sb.append(body).append("    }\n");
        return sb.toString();
    }

    /**
     * An {@code athrow} can raise any {@code Throwable}, and emitting it as a real Java
     * {@code throw} of a {@code Throwable}-typed expression is a checked-exception throw
     * (JLS 11.2.2). Methods that may throw declare it so the transpiled sources compile.
     */
    private String throwsClause() {
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn =
            insn.getNext()) {
            if (insn.getOpcode() == Opcodes.ATHROW) {
                return " throws Throwable";
            }
        }
        return "";
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
            return "void ";
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

    /** A Java string literal body for the constant (backslash, quotes and line breaks escaped). */
    private static String escapeJavaString(String s) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '\\' -> sb.append("\\\\");
                case '"' -> sb.append("\\\"");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                default -> sb.append(c);
            }
        }
        return sb.toString();
    }

    private String prologue() {
        StringBuilder sb = new StringBuilder();
        for (int slot : localSlots) {
            sb.append("        ").append(slotType(slot)).append(' ').append(localName(slot))
                    .append(";\n");
        }
        sb.append("        jvm.Local ").append(stackVar).append(" = new jvm.Local();\n");
        return sb.toString();
    }

    /** A try range with its catch clauses, recovered from the exception table (M3). */
    private record Region(int start, int end, List<Handler> handlers) {
    }

    /**
     * One catch clause. {@code index} is the bytecode index of the handler's leading
     * {@code astore} (consumed: the clause binds that slot), {@code end} is the first index
     * after the handler body, {@code type} the caught class (simple name, {@code Throwable}
     * for the catch-all used by finally inlining).
     */
    private record Handler(int index, int slot, String type, int end) {
    }

    /**
     * Recovers the exception regions (M3) from the exception table. Each {@code try} range
     * becomes one {@link Region} in javac's source order; the handler instructions are
     * consumed into the catch clause — their leading {@code astore} binds the catch variable,
     * which therefore gets no own local declaration. A handler runs from its first instruction
     * up to the next jump target, the next region start, or the end of the method.
     */
    private void analyzeTryCatch() {
        if (method.tryCatchBlocks == null || method.tryCatchBlocks.isEmpty()) {
            return;
        }
        // group table entries by try range; javac lists the catch clauses of one try in order
        Map<List<Integer>, List<TryCatchBlockNode>> byRange = new LinkedHashMap<>();
        for (TryCatchBlockNode block : method.tryCatchBlocks) {
            Integer start = labelIndex.get(block.start);
            Integer end = labelIndex.get(block.end);
            if (start == null || end == null || labelIndex.get(block.handler) == null) {
                throw new IllegalStateException(
                    "exception table label without index in " + method.name);
            }
            if (start >= end) {
                throw new IllegalStateException("empty try range in " + method.name);
            }
            byRange.computeIfAbsent(List.of(start, end), k -> new ArrayList<>()).add(block);
        }
        Set<Integer> regionStarts =
            new HashSet<>(byRange.keySet().stream().map(r -> r.get(0)).toList());
        List<Region> regions = new ArrayList<>();
        for (Map.Entry<List<Integer>, List<TryCatchBlockNode>> entry : byRange.entrySet()) {
            int start = entry.getKey().get(0);
            int end = entry.getKey().get(1);
            List<Handler> handlers = new ArrayList<>();
            List<Integer> handlerRange = new ArrayList<>();
            for (TryCatchBlockNode block : entry.getValue()) {
                int entryIdx = labelIndex.get(block.handler);
                int firstInsn = entryIdx;
                while (firstInsn < instructionCount && nodes.get(firstInsn).getOpcode() == -1) {
                    firstInsn++;
                }
                if (firstInsn >= instructionCount
                        || nodes.get(firstInsn).getOpcode() != Opcodes.ASTORE) {
                    throw new UnsupportedOperationException(
                        "exception handler in " + method.name + " must start with astore");
                }
                int handlerEnd = handlerExtent(firstInsn, regionStarts);
                int slot = ((VarInsnNode) nodes.get(firstInsn)).var;
                // the catch clause binds the slot: no separate local declaration
                localSlots.remove(slot);
                String type = block.type == null ? "Throwable" : simpleName(block.type);
                handlers.add(new Handler(firstInsn, slot, type, handlerEnd));
                for (int i = firstInsn; i < handlerEnd; i++) {
                    handlerRange.add(i);
                }
            }
            // handler instructions must not overlap the try body or an earlier handler range
            for (int i = start; i < end; i++) {
                if (handlerRange.contains(i) || consumed.contains(i)) {
                    throw new UnsupportedOperationException(
                        "handler overlapping a try body in " + method.name
                            + " is not supported in M3");
                }
            }
            regions.add(new Region(start, end, handlers));
            consumed.addAll(handlerRange);
        }
        regions.sort(Comparator.comparingInt(Region::start).thenComparingInt(Region::end));
        tryRegions.addAll(regions);
        // A goto_ target landing inside a handler body is resolved by truncation, not an abort:
        // handlerExtent stops the consumed span at the first target, so the emitted catch body
        // is straight-line by construction (targets ∩ consumed is empty — no dead guard needed),
        // the target's code becomes an ordinary guarded L<t> block outside the catch, and any
        // handler-body code referencing the catch-bound slot after the target fails the javac
        // round-trip loudly. Both shapes are pinned in S4ExceptionShapeTest.
    }

    /** The handler body [from, end) ends at the next jump target, region start, or end. */
    private int handlerExtent(int from, Set<Integer> regionStarts) {
        for (int i = from; i < instructionCount; i++) {
            if (targets.contains(i) || regionStarts.contains(i)) {
                return i;
            }
        }
        return instructionCount;
    }

    /** Emits {@code } catch (T v) { body } ... } for the region's catch clauses. */
    private void emitCatchClauses(Region region) {
        for (Handler handler : region.handlers()) {
            line("        } catch ("
                + handler.type() + " " + localName(handler.slot()) + ") {");
            emitHandlerBody(handler);
        }
        line("        }");
    }

    /** Emits the instructions of a catch clause's body (the handler without its astore). */
    private void emitHandlerBody(Handler handler) {
        boolean inLabeled = false;
        for (int i = handler.index() + 1; i < handler.end(); i++) {
            AbstractInsnNode insn = nodes.get(i);
            if (targets.contains(i)) {
                if (inLabeled) {
                    line("        }");
                }
                line("        L" + i + ": { if (false) { break L" + i + "; }");
                inLabeled = true;
            }
            if (insn.getOpcode() != -1) {
                emitInstruction(insn, i);
            }
        }
        if (inLabeled) {
            line("        }");
        }
    }

    /** The exception regions whose {@code try} starts at bytecode index {@code index}. */
    private List<Region> regionsStartingAt(int index) {
        return tryRegions.stream().filter(r -> r.start() == index).toList();
    }

    /** The exception regions whose {@code try} ends at (exclusive) bytecode index {@code index}. */
    private List<Region> regionsEndingAt(int index) {
        return tryRegions.stream().filter(r -> r.end() == index).toList();
    }

    private void emit() {
        int index = 0;
        boolean inLabeled = false;
        String pendingNew = null;
        boolean skippedDup = false;
        for (AbstractInsnNode insn = method.instructions.getFirst(); insn != null; insn =
            insn.getNext(), index++) {
            // M3: enter every try region that starts at this index
            for (Region region : regionsStartingAt(index)) {
                line("        try {");
            }
            // M3: handler instructions were emitted inside their catch clause
            if (consumed.contains(index)) {
                continue;
            }
            // M3: close every try region that ends at (exclusive) this index, before the next
            // instruction. A guard-labeled span crossing the boundary is closed first.
            if (!regionsEndingAt(index).isEmpty() && inLabeled) {
                line("        }");
                inLabeled = false;
            }
            for (Region region : regionsEndingAt(index)) {
                emitCatchClauses(region);
            }
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
        // M3: try regions whose end is the end of the method
        for (Region region : regionsEndingAt(instructionCount)) {
            if (inLabeled) {
                line("        }");
                inLabeled = false;
            }
            emitCatchClauses(region);
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
        // A mid-layout return/throw that ended up as the method's very last statement must lose
        // its `if (true) { }` wrapper: with nothing following, the wrapper would only make javac's
        // flow fall off the end of a non-void method ("missing return statement"). This happens
        // around try/catch regions, whose close resets the label-span tracking. The wrapper's only
        // job is keeping code after the statement reachable — there is none here.
        if (lastLine != null && (lastLine.startsWith("        if (true) { return ")
                || lastLine.startsWith("        if (true) { throw ")) && lastLine.endsWith("; }")) {
            body.setLength(body.length() - lastLine.length() - 1);
            line("        " + lastLine.substring("        if (true) { ".length(),
                lastLine.length() - " }".length()));
        }
    }

    /** Instructions that may appear inside a new+<init> pattern: argument pushes only. */
    private static boolean isConstructorArgumentPush(AbstractInsnNode insn) {
        return switch (insn.getOpcode()) {
            case Opcodes.ILOAD, Opcodes.ALOAD, Opcodes.LLOAD, Opcodes.DLOAD, Opcodes.FLOAD,
                    Opcodes.LDC, Opcodes.ICONST_M1, Opcodes.ICONST_0,
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
                } else if (cst instanceof Long v) {
                    line("        " + stackVar + ".pushL(" + v + "L);");
                } else if (cst instanceof Double v) {
                    line("        " + stackVar + ".pushD(" + v + ");");
                } else if (cst instanceof Float v) {
                    line("        " + stackVar + ".pushF(" + v + "f);");
                } else if (cst instanceof String v) {
                    line("        " + stackVar + ".push(\"" + escapeJavaString(v) + "\");");
                } else {
                    unsupported(insn);
                }
            }
            case Opcodes.ILOAD -> {
                VarInsnNode var = (VarInsnNode) insn;
                String name = localName(var.var);
                if (slotType(var.var).equals("boolean")) {
                    // JVM booleans are ints (0/1) on the operand stack; a boolean-typed local
                    // slot must be extracted, never boxed into push(Object)
                    line("        " + stackVar + ".push((" + name + " ? 1 : 0));");
                } else {
                    line("        " + stackVar + ".push(" + name + ");");
                }
            }
            case Opcodes.ALOAD ->
                line("        " + stackVar + ".push(" + localName(((VarInsnNode) insn).var)
                    + ");");
            case Opcodes.LLOAD ->
                line("        " + stackVar + ".pushL(" + localName(((VarInsnNode) insn).var)
                    + ");");
            case Opcodes.DLOAD ->
                line("        " + stackVar + ".pushD(" + localName(((VarInsnNode) insn).var)
                    + ");");
            case Opcodes.FLOAD ->
                line("        " + stackVar + ".pushF(" + localName(((VarInsnNode) insn).var)
                    + ");");
            case Opcodes.ISTORE -> {
                VarInsnNode var = (VarInsnNode) insn;
                String name = localName(var.var);
                if (slotType(var.var).equals("boolean")) {
                    // store the int 0/1 back into a boolean-typed slot
                    line("        " + name + " = (" + stackVar + ".pop() != 0);");
                } else {
                    line("        " + name + " = " + stackVar + ".pop();");
                }
            }
            case Opcodes.LSTORE ->
                line("        " + localName(((VarInsnNode) insn).var) + " = " + stackVar
                    + ".popL();");
            case Opcodes.DSTORE ->
                line("        " + localName(((VarInsnNode) insn).var) + " = " + stackVar
                    + ".popD();");
            case Opcodes.FSTORE ->
                line("        " + localName(((VarInsnNode) insn).var) + " = " + stackVar
                    + ".popF();");
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
            case Opcodes.TABLESWITCH -> emitTableSwitch((TableSwitchInsnNode) insn);
            case Opcodes.LOOKUPSWITCH -> emitLookupSwitch((LookupSwitchInsnNode) insn);
            case Opcodes.IADD, Opcodes.ISUB, Opcodes.IMUL, Opcodes.IDIV, Opcodes.IREM, Opcodes.INEG,
                    Opcodes.IAND, Opcodes.IOR, Opcodes.IXOR, Opcodes.ISHL, Opcodes.ISHR,
                    Opcodes.IUSHR, Opcodes.LADD, Opcodes.LSUB, Opcodes.LMUL, Opcodes.LDIV,
                    Opcodes.LREM, Opcodes.LNEG, Opcodes.LCMP, Opcodes.DADD, Opcodes.DSUB,
                    Opcodes.DMUL, Opcodes.DDIV, Opcodes.DREM, Opcodes.DNEG, Opcodes.DCMPG,
                    Opcodes.DCMPL, Opcodes.FADD, Opcodes.FSUB, Opcodes.FMUL, Opcodes.FDIV,
                    Opcodes.FREM, Opcodes.FNEG, Opcodes.FCMPG, Opcodes.FCMPL, Opcodes.I2L,
                    Opcodes.L2I, Opcodes.I2F, Opcodes.F2I, Opcodes.F2D, Opcodes.D2F, Opcodes.I2D,
                    Opcodes.D2I, Opcodes.L2F, Opcodes.F2L, Opcodes.L2D, Opcodes.D2L ->
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
            case Opcodes.GETSTATIC -> emitGetStatic((FieldInsnNode) insn);
            case Opcodes.PUTSTATIC -> emitPutStatic((FieldInsnNode) insn);
            case Opcodes.CHECKCAST -> emitCheckCast((TypeInsnNode) insn);
            case Opcodes.INSTANCEOF -> emitInstanceOf((TypeInsnNode) insn);
            case Opcodes.NEWARRAY -> emitNewArray((IntInsnNode) insn);
            case Opcodes.IALOAD -> emitIaload();
            case Opcodes.IASTORE -> emitIastore();
            case Opcodes.LALOAD -> emitLaload();
            case Opcodes.LASTORE -> emitLastore();
            case Opcodes.ARRAYLENGTH -> emitArrayLength();
            case Opcodes.ATHROW ->
                line("        " + returnStatement(index,
                    "throw (Throwable) " + stackVar + ".popRef();"));
            case Opcodes.IRETURN ->
                line("        " + returnStatement(index, "return " + stackVar + ".top();"));
            case Opcodes.LRETURN ->
                line("        " + returnStatement(index, "return " + stackVar + ".topL();"));
            case Opcodes.DRETURN ->
                line("        " + returnStatement(index, "return " + stackVar + ".topD();"));
            case Opcodes.FRETURN ->
                line("        " + returnStatement(index, "return " + stackVar + ".topF();"));
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
            case Opcodes.DUP_X1 ->
                line("        " + stackVar + ".dup_x1();");
            case Opcodes.DUP_X2 ->
                line("        " + stackVar + ".dup_x2();");
            case Opcodes.DUP2 ->
                line("        " + stackVar + ".dup2();");
            case Opcodes.DUP2_X1 ->
                line("        " + stackVar + ".dup2_x1();");
            case Opcodes.DUP2_X2 ->
                line("        " + stackVar + ".dup2_x2();");
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

    /** getstatic: pushes the static field value (real Java static access). */
    private void emitGetStatic(FieldInsnNode field) {
        line("        " + stackVar + ".push(" + staticValueExpression(field) + ");");
    }

    /**
     * putstatic: pops the value (on top) and writes the real static field. A boolean field is
     * materialized from the JVM's 0/1 representation; category-2 static values abort loudly.
     */
    private void emitPutStatic(FieldInsnNode field) {
        Type type = Type.getType(field.desc);
        if (type.getSort() == Type.BOOLEAN) {
            String value = freshTemp("$v");
            line("        int " + value + " = " + stackVar + ".pop();");
            line("        " + staticAccess(field) + " = " + value + " != 0;");
            return;
        }
        if (type.getSort() != Type.INT && type.getSort() != Type.OBJECT
                && type.getSort() != Type.ARRAY) {
            throw new UnsupportedOperationException(
                "Unsupported putstatic value type in " + method.name + ": " + field.desc);
        }
        String value = freshTemp("$v");
        line("        " + declaredTemp(type, value) + ";");
        line("        " + staticAccess(field) + " = " + value + ";");
    }

    /** The static field read, int-normalized for {@code push} ({@code boolean} → 0/1). */
    private String staticValueExpression(FieldInsnNode field) {
        Type type = Type.getType(field.desc);
        String access = staticAccess(field);
        return switch (type.getSort()) {
            case Type.BOOLEAN -> "(" + access + " ? 1 : 0)";
            case Type.INT, Type.BYTE, Type.SHORT, Type.CHAR, Type.OBJECT, Type.ARRAY -> access;
            default -> throw new UnsupportedOperationException(
                "Unsupported getstatic value type in " + method.name + ": " + field.desc);
        };
    }

    /** Static field access expression {@code Owner.field}. */
    private static String staticAccess(FieldInsnNode field) {
        return jvmTypeName(Type.getObjectType(field.owner)) + "." + field.name;
    }

    /**
     * checkcast: pops the reference, casts it to the target type (a real Java cast — its
     * ClassCastException obligation is the point of the instruction, ruled out by
     * {@code runtimeExceptions:ban} in proofs) and pushes the typed reference back.
     * Array casts belong to the arrays slice and abort loudly.
     */
    private void emitCheckCast(TypeInsnNode cast) {
        if (cast.desc.startsWith("[")) {
            unsupported(new TypeInsnNode(Opcodes.CHECKCAST, cast.desc));
        }
        String obj = freshTemp("$o");
        String t = jvmTypeName(Type.getObjectType(cast.desc));
        line("        " + t + " " + obj + " = (" + t + ") " + stackVar + ".popRef();");
        line("        " + stackVar + ".push(" + obj + ");");
    }

    /**
     * instanceof: pops the reference and pushes the JVM's int result (0/1) of the real
     * {@code instanceof} expression ({@code null} is never an instance, matching the JVM).
     */
    private void emitInstanceOf(TypeInsnNode insn) {
        if (insn.desc.startsWith("[")) {
            unsupported(insn);
        }
        String obj = freshTemp("$o");
        String t = jvmTypeName(Type.getObjectType(insn.desc));
        line("        Object " + obj + " = (Object) " + stackVar + ".popRef();");
        line("        " + stackVar + ".push(" + obj + " instanceof " + t + " ? 1 : 0);");
    }

    /**
     * newarray: pops the length and pushes the real allocation. The M2 arrays slice covers
     * {@code int[]} ({@code T_INT}) only; every other element type aborts loudly.
     */
    private void emitNewArray(IntInsnNode insn) {
        if (insn.operand != Opcodes.T_INT) {
            throw new UnsupportedOperationException(
                "newarray with atype " + insn.operand + " in " + method.name
                    + ": only int[] (T_INT) is supported in M2");
        }
        String arr = freshTemp("$a");
        line("        int[] " + arr + " = new int[" + stackVar + ".pop()];");
        line("        " + stackVar + ".push(" + arr + ");");
    }

    /** iaload: pops index then array reference and pushes the real {@code a[i]} read. */
    private void emitIaload() {
        String idx = freshTemp("$i");
        String arr = freshTemp("$a");
        line("        int " + idx + " = " + stackVar + ".pop();");
        line("        int[] " + arr + " = (int[]) " + stackVar + ".popRef();");
        line("        " + stackVar + ".push(" + arr + "[" + idx + "]);");
    }

    /** iastore: pops value, index and array reference and performs the real {@code a[i] = v}. */
    private void emitIastore() {
        String val = freshTemp("$v");
        String idx = freshTemp("$i");
        String arr = freshTemp("$a");
        line("        int " + val + " = " + stackVar + ".pop();");
        line("        int " + idx + " = " + stackVar + ".pop();");
        line("        int[] " + arr + " = (int[]) " + stackVar + ".popRef();");
        line("        " + arr + "[" + idx + "] = " + val + ";");
    }

    /** laload: pops index then array reference and pushes the real {@code a[i]} long read. */
    private void emitLaload() {
        String idx = freshTemp("$i");
        String arr = freshTemp("$a");
        line("        int " + idx + " = " + stackVar + ".pop();");
        line("        long[] " + arr + " = (long[]) " + stackVar + ".popRef();");
        line("        " + stackVar + ".pushL(" + arr + "[" + idx + "]);");
    }

    /** lastore: pops value, index and array reference and performs the real {@code a[i] = v}. */
    private void emitLastore() {
        String val = freshTemp("$v");
        String idx = freshTemp("$i");
        String arr = freshTemp("$a");
        line("        long " + val + " = " + stackVar + ".popL();");
        line("        int " + idx + " = " + stackVar + ".pop();");
        line("        long[] " + arr + " = (long[]) " + stackVar + ".popRef();");
        line("        " + arr + "[" + idx + "] = " + val + ";");
    }

    /** arraylength: pops the array reference and pushes its {@code .length}. */
    private void emitArrayLength() {
        String arr = freshTemp("$a");
        line("        int[] " + arr + " = (int[]) " + stackVar + ".popRef();");
        line("        " + stackVar + ".push(" + arr + ".length);");
    }

    /**
     * tableswitch (M3): pops the selector and dispatches on its value as an if-chain of
     * {@code if (sel == key) { jvm.Local.goto_(pc); }} over the dense key range, followed by an
     * unconditional {@code goto_(dflt)}. Every case/default label is a {@code L<pc>} target the
     * {@code GotoSpliceRule} resolves, so the canonical linear layout is preserved.
     */
    private void emitTableSwitch(TableSwitchInsnNode insn) {
        String sel = freshTemp("$s");
        line("        int " + sel + " = " + stackVar + ".pop();");
        int key = insn.min;
        for (LabelNode label : insn.labels) {
            line("        if (" + sel + " == " + key + ") { jvm.Local.goto_("
                + labelIndex.get(label) + "); }");
            key++;
        }
        line("        jvm.Local.goto_(" + labelIndex.get(insn.dflt) + ");");
    }

    /** lookupswitch: as {@link #emitTableSwitch}, but over the sparse key list. */
    private void emitLookupSwitch(LookupSwitchInsnNode insn) {
        String sel = freshTemp("$s");
        line("        int " + sel + " = " + stackVar + ".pop();");
        for (int i = 0; i < insn.keys.size(); i++) {
            line("        if (" + sel + " == " + insn.keys.get(i) + ") { jvm.Local.goto_("
                + labelIndex.get(insn.labels.get(i)) + "); }");
        }
        line("        jvm.Local.goto_(" + labelIndex.get(insn.dflt) + ");");
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
        lastLine = text;
    }

    /** The raw text of the most recently appended body line (for tail post-processing). */
    private String lastLine = null;

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
