/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.transpiler;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;

/**
 * Generates <em>stub classes</em> for types the transpiled output references but that are
 * neither part of the transpiled input nor provided by the JDK / the {@code jvm.Local} runtime.
 * The emitted Java must compile (every test round-trips it through javac), so a referenced
 * external type without a stub would fail loudly — exactly what the stubs prevent.
 * <p>
 * A stub carries exactly the members the emitted output actually accesses — fields from
 * {@code get/putfield} and {@code get/putstatic} sites, methods from {@code invoke*} sites and
 * constructors from {@code new T}+{@code <init>} fusions — with default-valued bodies
 * ({@code return 0; nullptr}/empty). It models the <em>shape</em> for compilation only; method
 * contracts of the original type are not carried over (that is the later spec-stubbing step).
 */
public final class StubGenerator {

    /** Internal-name prefixes that compile natively and therefore never need a stub. */
    private static final List<String> PROVIDED_PREFIXES =
        List.of("java/", "javax/", "jdk/", "sun/", "com/sun/", "jvm/");

    private StubGenerator() {
    }

    /**
     * Scans the transpiled class nodes for every external type reference and every member site
     * the emitted code will access. Only types that need a stub are present in the result.
     *
     * @param transpiled the class nodes being transpiled (their internal names are provided)
     * @return stubs keyed by internal name, ordered deterministically
     */
    public static Map<String, StubSpec> collect(List<ClassNode> transpiled,
            Set<String> providedInternalNames) {
        Map<String, StubSpec> stubs = new TreeMap<>();
        for (ClassNode classNode : transpiled) {
            typeNeed(stubs, classNode.superName);
            for (String itf : classNode.interfaces) {
                typeNeed(stubs, itf);
            }
            for (FieldNode field : classNode.fields) {
                if ((field.access & (Opcodes.ACC_SYNTHETIC | Opcodes.ACC_ENUM)) != 0) {
                    continue;
                }
                typeNeed(stubs, Type.getType(field.desc));
            }
            for (MethodNode method : classNode.methods) {
                if (method.name.equals("<clinit>")) {
                    continue;
                }
                // method signature: return + parameter types
                Type[] args = Type.getArgumentTypes(method.desc);
                typeNeed(stubs, Type.getReturnType(method.desc));
                for (Type arg : args) {
                    typeNeed(stubs, arg);
                }
                // local slots (receiver/argument types the emitted bodies reference) and the
                // instruction operands (field/method/type accesses)
                if (method.localVariables != null) {
                    method.localVariables.forEach(
                        lv -> typeNeed(stubs, Type.getType(lv.desc)));
                }
                for (AbstractInsnNode insn : method.instructions) {
                    switch (insn.getOpcode()) {
                        case Opcodes.GETFIELD, Opcodes.PUTFIELD, Opcodes.GETSTATIC,
                                Opcodes.PUTSTATIC -> {
                            FieldInsnNode field = (FieldInsnNode) insn;
                            typeNeed(stubs, field.owner);
                            typeNeed(stubs, Type.getType(field.desc));
                            member(stubs, field);
                        }
                        case Opcodes.INVOKEVIRTUAL, Opcodes.INVOKESPECIAL, Opcodes.INVOKESTATIC,
                                Opcodes.INVOKEINTERFACE -> {
                            MethodInsnNode call = (MethodInsnNode) insn;
                            typeNeed(stubs, call.owner);
                            typeNeed(stubs, Type.getReturnType(call.desc));
                            for (Type arg : Type.getArgumentTypes(call.desc)) {
                                typeNeed(stubs, arg);
                            }
                            member(stubs, call);
                        }
                        case Opcodes.NEW, Opcodes.ANEWARRAY, Opcodes.CHECKCAST,
                                Opcodes.INSTANCEOF -> {
                            TypeInsnNode cast = (TypeInsnNode) insn;
                            if (!cast.desc.startsWith("[")) {
                                typeNeed(stubs, cast.desc);
                            }
                        }
                        default -> {
                            // everything else carries no type references
                        }
                    }
                }
            }
        }
        for (StubSpec stub : new java.util.ArrayList<>(stubs.values())) {
            if (isProvided(stub.internalName)
                    || providedInternalNames.contains(stub.internalName)) {
                stubs.remove(stub.internalName);
            }
        }
        return stubs;
    }

    /** Reads the type reference (if it is an object type, i.e. not a primitive/array). */
    private static void typeNeed(Map<String, StubSpec> stubs, Type type) {
        if (type.getSort() == Type.OBJECT) {
            typeNeed(stubs, type.getInternalName());
        }
    }

    /** Records that the emitted code references an internal name as a type. */
    private static void typeNeed(Map<String, StubSpec> stubs, String internalName) {
        if (internalName == null) {
            return;
        }
        // keep stubs for genuinely external types only (primitives/arrays never reach here)
        if (isProvided(internalName)) {
            return;
        }
        stubs.computeIfAbsent(internalName, StubSpec::new);
    }

    private static boolean isProvided(String internalName) {
        for (String prefix : PROVIDED_PREFIXES) {
            if (internalName.startsWith(prefix)) {
                return true;
            }
        }
        return false;
    }

    private static void member(Map<String, StubSpec> stubs, FieldInsnNode field) {
        StubSpec stub = stubs.get(field.owner);
        if (stub == null) {
            return;
        }
        stub.typeOnly = false;
        String decl = MethodTranspiler.jvmTypeName(Type.getType(field.desc)) + " " + field.name;
        if ((field.getOpcode() == Opcodes.GETSTATIC || field.getOpcode() == Opcodes.PUTSTATIC)) {
            stub.staticFields.add(decl);
        } else {
            stub.instanceFields.add(decl);
        }
    }

    private static void member(Map<String, StubSpec> stubs, MethodInsnNode call) {
        StubSpec stub = stubs.get(call.owner);
        if (stub == null) {
            return;
        }
        stub.typeOnly = false;
        if (call.name.equals("<init>")) {
            stub.constructors.add(parameterList(call.desc));
            return;
        }
        Type ret = Type.getReturnType(call.desc);
        String decl =
            MethodTranspiler.jvmTypeName(ret) + " " + call.name + parameterList(call.desc);
        if (call.getOpcode() == Opcodes.INVOKESTATIC) {
            stub.staticMethods.add(decl);
        } else {
            stub.instanceMethods.add(decl);
        }
    }

    private static String parameterList(String desc) {
        Type[] args = Type.getArgumentTypes(desc);
        var sb = new StringBuilder("(");
        for (int i = 0; i < args.length; i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(MethodTranspiler.jvmTypeName(args[i])).append(" p").append(i);
        }
        return sb.append(')').toString();
    }

    /**
     * The Java source of a stub: a default-package class carrying exactly the members the
     * emitted output accesses, with default-valued bodies so the output compiles.
     */
    public static String emitSource(StubSpec stub) {
        var sb = new StringBuilder();
        sb.append("// Generated by the KeY JVM transpiler: stub for the referenced type ")
                .append(stub.internalName)
                .append(" (not part of the transpiled input; member bodies are default-valued so\n")
                .append("// the emitted output compiles — method contracts of the original type are"
                    + " not carried over).\n");
        sb.append("public class ").append(MethodTranspiler.jvmTypeName(
            Type.getObjectType(stub.internalName))).append(" {\n");
        emitMembers(sb, stub.instanceFields, null);
        emitMethods(sb, stub.instanceMethods);
        sb.append('\n');
        emitMembers(sb, stub.staticFields, "static ");
        emitMethods(sb, stub.staticMethods, "static ");
        for (String params : stub.constructors) {
            sb.append("    public ").append(MethodTranspiler.jvmTypeName(
                Type.getObjectType(stub.internalName))).append(params).append(" { }\n");
        }
        return sb.append("}\n").toString();
    }

    private static void emitMembers(StringBuilder sb, Set<String> members, String modifier) {
        for (String decl : members) {
            sb.append("    public ").append(modifier == null ? "" : modifier).append(decl)
                    .append(";\n");
        }
    }

    private static void emitMethods(StringBuilder sb, Set<String> methods) {
        emitMethods(sb, methods, "");
    }

    private static void emitMethods(StringBuilder sb, Set<String> methods, String modifier) {
        for (String decl : methods) {
            String ret = decl.substring(0, decl.indexOf(' '));
            sb.append("    public ").append(modifier).append(decl).append(" { ")
                    .append(defaultValue(ret)).append(" }\n");
        }
    }

    /** The default return expression for a stub method body, by return type name. */
    private static String defaultValue(String retType) {
        switch (retType) {
            case "long":
                return "return 0L;";
            case "float":
                return "return 0F;";
            case "double":
                return "return 0D;";
            case "boolean":
                return "return false;";
            case "int", "byte", "short", "char":
                return "return 0;";
            case "void":
                return "";
            default:
                return "return null;";
        }
    }

    /** One stub class: the external type and the members the emitted output accesses. */
    public static final class StubSpec {
        /** The referenced external type, internal form, e.g. {@code com/example/Library}. */
        public final String internalName;
        final Set<String> instanceFields = new LinkedHashSet<>();
        final Set<String> staticFields = new LinkedHashSet<>();
        final Set<String> instanceMethods = new LinkedHashSet<>();
        final Set<String> staticMethods = new LinkedHashSet<>();
        /**
         * Constructor parameter lists, e.g. {@code "(int p0, Gadget p1)"}; keys are the source
         * order.
         */
        final Set<String> constructors = new LinkedHashSet<>();
        boolean typeOnly = true;

        StubSpec(String internalName) {
            this.internalName = internalName;
        }

        @Override
        public String toString() {
            return internalName;
        }
    }
}
