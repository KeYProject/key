/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

/**
 * M3 spike-S4 residue: pins the {@code MethodTranspiler} behavior on exception-table shapes
 * javac never emits for normal source (hand-written bytecode only) and which structured Java
 * {@code try/catch} therefore cannot express directly:
 * <ul>
 * <li>{@code handlerRangeOverlappingTryBodyAbortsLoudly} — a handler whose range overlaps
 * another try region's body is rejected with {@link UnsupportedOperationException};</li>
 * <li>{@code branchTargetInsideHandlerTruncatesAtTheTarget} — a jump target landing inside a
 * handler's linear span truncates the catch body right before the target (the emitted catch is
 * straight-line by construction; the target's code becomes an ordinary guarded {@code L<t>}
 * block). This is the test-pinned resolution of the dead {@code targets ∩ consumed} guard: the
 * {@code handlerExtent} truncation makes that intersection empty by construction.</li>
 * </ul>
 * Classes are synthesized with ASM so the exception tables can be crafted freely (javac would
 * never produce them).
 */
class S4ExceptionShapeTest {

    @TempDir
    Path tmpDir;

    @Test
    void handlerRangeOverlappingTryBodyAbortsLoudly() throws Exception {
        Path classes = tmpDir.resolve("classes");
        Files.createDirectories(classes);
        Files.write(classes.resolve("Overlap.class"), overlapClass());

        assertThatThrownBy(() -> Transpiler.transpile(List.of(classes.resolve("Overlap.class")),
            tmpDir.resolve("out")))
                .isInstanceOf(UnsupportedOperationException.class)
                .hasMessageContaining("handler overlapping a try body");
    }

    @Test
    void branchTargetInsideHandlerTruncatesAtTheTarget() throws Exception {
        Path classes = tmpDir.resolve("classes");
        Files.createDirectories(classes);
        Files.write(classes.resolve("BranchIntoHandler.class"), branchIntoHandlerClass());

        Path out = tmpDir.resolve("out");
        List<Path> emitted =
            Transpiler.transpile(List.of(classes.resolve("BranchIntoHandler.class")), out);

        Path source = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("BranchIntoHandler.java"))
                .findFirst().orElseThrow();
        String s = Files.readString(source, StandardCharsets.UTF_8);
        // the handler body is truncated right before the target: only `push(2)` stays caught
        assertThat(s).contains("catch (Exception local_1) {")
                .contains("stk.push(2);")
                .contains("L6: { if (false) { break L6; }");
    }

    // --- synthetic classes ------------------------------------------------------------

    /** Two overlapping try ranges where the second try body runs through the first handler. */
    private static byte[] overlapClass() {
        ClassWriter cw = new ClassWriter(0);
        cw.visit(Opcodes.V17, Opcodes.ACC_PUBLIC | Opcodes.ACC_SUPER, "Overlap", null,
            "java/lang/Object", null);
        MethodVisitor mv = cw.visitMethod(Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, "f", "(I)I",
            null, null);
        Label sA = new Label();
        Label sB = new Label();
        Label eA = new Label();
        Label hA = new Label();
        Label eB = new Label();
        Label hB = new Label();
        mv.visitCode();
        mv.visitLabel(sA);
        mv.visitLabel(sB);
        mv.visitInsn(Opcodes.ICONST_1); // 2
        mv.visitLabel(eA); // 3 tryA [0,4): body {2}
        mv.visitInsn(Opcodes.ICONST_2); // 4
        mv.visitLabel(hA); // 5
        mv.visitVarInsn(Opcodes.ASTORE, 1); // 6 handler A
        mv.visitInsn(Opcodes.NOP); // 7
        mv.visitInsn(Opcodes.ICONST_3); // 8
        mv.visitLabel(eB); // 9 tryB [2,9): body {4,6,8}
        mv.visitLabel(hB); // 10
        mv.visitVarInsn(Opcodes.ASTORE, 1); // 11 handler B
        mv.visitInsn(Opcodes.ICONST_0); // 12
        mv.visitInsn(Opcodes.IRETURN); // 13
        mv.visitTryCatchBlock(sA, eA, hA, "java/lang/Exception");
        mv.visitTryCatchBlock(sB, eB, hB, "java/lang/Exception");
        mv.visitMaxs(2, 2);
        mv.visitEnd();
        cw.visitEnd();
        return cw.toByteArray();
    }

    /**
     * A goto landing in the middle of a handler's linear span. Read-back node layout (the two
     * consecutive labels before the handler collapse into one during the write/read round-trip):
     * {@code 0 s, 1 BIPUSH 1, 2 GOTO t, 3 e/handler, 4 ASTORE 1, 5 BIPUSH 2, 6 t, 7 IRETURN};
     * try [0,3) → handler at 3, so the catch owns only {@code push(2)} and the target at 6
     * truncates the handler (becoming a guarded {@code L6} block outside the catch).
     */
    private static byte[] branchIntoHandlerClass() {
        ClassWriter cw = new ClassWriter(0);
        cw.visit(Opcodes.V17, Opcodes.ACC_PUBLIC | Opcodes.ACC_SUPER, "BranchIntoHandler", null,
            "java/lang/Object", null);
        MethodVisitor mv = cw.visitMethod(Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, "f", "()I",
            null, null);
        Label s = new Label();
        Label e = new Label();
        Label t = new Label();
        mv.visitCode();
        mv.visitLabel(s);
        mv.visitIntInsn(Opcodes.BIPUSH, 1); // 1
        mv.visitJumpInsn(Opcodes.GOTO, t); // 2
        mv.visitLabel(e); // 3 handler start (try [0,3))
        mv.visitVarInsn(Opcodes.ASTORE, 1); // 4 handler
        mv.visitIntInsn(Opcodes.BIPUSH, 2); // 5
        mv.visitLabel(t); // 6 target (inside handler span)
        mv.visitInsn(Opcodes.IRETURN); // 7
        mv.visitTryCatchBlock(s, e, e, "java/lang/Exception");
        mv.visitMaxs(2, 2);
        mv.visitEnd();
        cw.visitEnd();
        return cw.toByteArray();
    }
}
