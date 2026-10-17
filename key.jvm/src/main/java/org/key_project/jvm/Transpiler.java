/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.jvm.transpiler.MethodTranspiler;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.MethodNode;

/**
 * Facade of the bytecode transpiler. It reads one or more {@code .class} files / JARs and emits
 * compilable Java source (plus a copy of the {@code jvm.Local} runtime and its JML contracts) into
 * an output directory.
 *
 * <p>
 * The M1 pipeline reads each class with ASM, emits every non-constructor method in the
 * <em>canonical linear layout</em> (mnemonic calls on a {@code jvm.Local}, labels + guarded label
 * blocks, {@code goto_} calls), and copies the {@code jvm.Local} runtime into
 * {@code <output>/jvm/Local.java}. The output is expected to compile with {@code javac} and is
 * intended to be re-parsed and proved by KeY with the {@code java-jvm} profile.
 */
public final class Transpiler {

    /** Classpath location of the runtime source copied into every output folder. */
    public static final String LOCAL_RUNTIME_RESOURCE =
        "/org/key_project/jvm/runtime/jvm/Local.java";

    private Transpiler() {
    }

    /**
     * Transpiles the given class inputs into {@code outputDir}.
     *
     * @param inputs the {@code .class}/JAR paths to read
     * @param outputDir the directory to write the emitted Java into (created if missing)
     * @return the paths of the emitted top-level Java sources (excluding the {@code jvm.Local}
     *         runtime copy)
     */
    public static List<Path> transpile(List<Path> inputs, Path outputDir) {
        return transpile(inputs, outputDir, List.of());
    }

    /**
     * Transpiles the given class inputs into {@code outputDir}, inlining the JML method
     * contracts found in {@code specSources} (typically the original {@code .java} sources,
     * whose contracts {@code javac} could not retain) in front of the matching emitted
     * methods.
     *
     * @param inputs the {@code .class}/JAR paths to read
     * @param outputDir the directory to write the emitted Java into (created if missing)
     * @param specSources original Java sources to take JML comments from (may be empty)
     * @return the paths of the emitted top-level Java sources (excluding the {@code jvm.Local}
     *         runtime copy)
     */
    public static List<Path> transpile(List<Path> inputs, Path outputDir,
            List<Path> specSources) {
        try {
            Files.createDirectories(outputDir);
            copyLocalRuntime(outputDir);

            List<Map<String, String>> specsByClass = specSources.stream().map(Transpiler::readSpecs)
                    .toList();
            List<Path> emitted = new ArrayList<>();
            for (Path input : inputs) {
                byte[] bytes = Files.readAllBytes(input);
                ClassNode classNode = new ClassNode();
                new ClassReader(bytes).accept(classNode, 0);

                String simpleName = simpleName(classNode.name);
                String source = emitClass(classNode, specsByClass);
                Path out = outputDir.resolve(simpleName + ".java");
                Files.writeString(out, source);
                emitted.add(out);
            }
            return emitted;
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /**
     * Maps method names to the JML {@code block-comment} contracts directly above their signature.
     */
    static Map<String, String> readSpecs(Path javaSource) {
        String src;
        try {
            src = Files.readString(javaSource);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        Map<String, String> specs = new LinkedHashMap<>();
        // a JML block comment, then optional modifiers, then <type> <name>( — i.e. a method
        // header. Fields cannot match ('name(' is required); a constructor's JML maps to its
        // simple name, which the transpiler never emits (M1 skips <init>), so it is harmless.
        java.util.regex.Matcher m = java.util.regex.Pattern.compile(
            "/\\*@(.*?)@\\*/\\s*((?:\\w+\\s+)*[\\w$<>\\[\\]\\.]+\\s+)(\\w+)\\s*\\(",
            java.util.regex.Pattern.DOTALL)
                .matcher(src);
        while (m.find()) {
            String jml = m.group(1);
            String name = m.group(3);
            specs.putIfAbsent(name, "/*@" + jml + "@*/");
        }
        return specs;
    }

    /**
     * Emits the Java source for a class: instance/static fields, then explicit constructors,
     * then all methods with bytecode.
     */
    private static String emitClass(ClassNode classNode,
            List<Map<String, String>> specsByClass) {
        var members = new ArrayList<String>();

        // fields (non-synthetic, non-enum): real Java fields; `final` is dropped because the
        // emitted class has no initialization guaranteeing blank finals in the Java sense
        for (FieldNode field : classNode.fields) {
            if ((field.access & (Opcodes.ACC_SYNTHETIC | Opcodes.ACC_ENUM)) != 0) {
                continue;
            }
            String mods = (field.access & Opcodes.ACC_STATIC) != 0 ? "public static " : "public ";
            members.add("    " + mods + MethodTranspiler.jvmTypeName(Type.getType(field.desc))
                + " " + field.name + ";\n");
        }

        for (MethodNode method : classNode.methods) {
            if (method.name.equals("<clinit>")) {
                continue;
            }
            if (method.name.equals("<init>") && isTrivialDefaultCtor(method)) {
                // javac's implicit `Point() { super(); }` — nothing to prove, nothing emitted;
                // keeps the M1 output (and its fixtures) unchanged
                continue;
            }
            boolean abstractOrNative =
                (method.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0;
            if (abstractOrNative || method.instructions.size() == 0) {
                continue;
            }
            boolean isStatic = (method.access & Opcodes.ACC_STATIC) != 0;
            String body = new MethodTranspiler(method, isStatic, classNode.name).transpile();
            // a constructor's JML contract is keyed by the simple class name in the spec source
            String specKey = method.name.equals("<init>") ? simpleName(classNode.name)
                    : method.name;
            String spec = joinSpecs(specsByClass, specKey);
            members.add(spec == null ? body : spec + "\n" + body);
        }
        if (members.isEmpty()) {
            throw new UnsupportedOperationException(
                "Class " + classNode.name + " has no transpilable members (M1).");
        }

        String packageDecl = "";
        int slash = classNode.name.lastIndexOf('/');
        if (slash > 0) {
            packageDecl =
                "package " + classNode.name.substring(0, slash).replace('/', '.') + ";\n\n";
        }

        StringBuilder sb = new StringBuilder(packageDecl);
        sb.append("// Generated by the KeY JVM transpiler from ").append(classNode.name)
                .append('\n');
        sb.append("public class ").append(simpleName(classNode.name)).append(" {\n");
        for (String m : members) {
            sb.append(m).append('\n');
        }
        return sb.append("}\n").toString();
    }

    /** The canonical javac default constructor: {@code aload_0; invokespecial <init>; return}. */
    private static boolean isTrivialDefaultCtor(MethodNode method) {
        if (Type.getArgumentTypes(method.desc).length != 0) {
            return false;
        }
        int ops = 0;
        for (AbstractInsnNode insn : method.instructions) {
            if (insn.getOpcode() != -1) {
                ops++;
            }
        }
        return ops == 3;
    }

    private static String joinSpecs(List<Map<String, String>> specsByClass, String methodName) {
        for (Map<String, String> specs : specsByClass) {
            String s = specs.get(methodName);
            if (s != null) {
                return s;
            }
        }
        return null;
    }

    private static String simpleName(String internalName) {
        int slash = internalName.lastIndexOf('/');
        return slash < 0 ? internalName : internalName.substring(slash + 1);
    }

    private static void copyLocalRuntime(Path outputDir) throws IOException {
        Path target = outputDir.resolve("jvm/Local.java");
        if (Files.exists(target)) {
            return;
        }
        Files.createDirectories(target.getParent());
        try (InputStream in = Transpiler.class.getResourceAsStream(LOCAL_RUNTIME_RESOURCE)) {
            if (in == null) {
                throw new IllegalStateException(
                    "Missing runtime resource " + LOCAL_RUNTIME_RESOURCE);
            }
            Files.copy(in, target);
        }
    }
}
