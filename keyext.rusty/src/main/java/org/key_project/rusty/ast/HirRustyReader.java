/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.Comparator;

import org.key_project.logic.Namespace;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.RustyBlock;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.parser.hir.Crate;

import org.jspecify.annotations.NonNull;

public class HirRustyReader {
    private final Services services;

    public HirRustyReader(Services services, NamespaceSet nss) {
        this.services = services;
    }

    public Services getServices() {
        return services;
    }

    /**
     * parses a given RustyBlock using the context to determine the right references
     *
     * @param block a String describing a java block
     * @param context recoder.java.CompilationUnit in which the block has to be interprested
     * @return the parsed and resolved JavaBlock
     */
    public RustyBlock readBlock(String block, Context context) throws IOException {
        var fn = context.buildFunction(block);
        Path tmpDir = Files.createTempDirectory("KeYTempFileMod_" + block.hashCode());
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            try (var s = Files.walk(tmpDir)) {
                s.sorted(Comparator.reverseOrder()).forEach(path -> {
                    try {
                        Files.delete(path);
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                });
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }));
        Files.copy(Path.of("./src/main/resources/rust-toolchain.toml"),
            tmpDir.resolve("rust-toolchain.toml"));
        Files.copy(Path.of("./src/main/resources/Cargo.toml"), tmpDir.resolve("Cargo.toml"));
        Path src = tmpDir.resolve("src");
        Files.createDirectory(src);
        Path lib = Files.createFile(src.resolve("lib.rs"));
        Files.writeString(lib, fn, StandardCharsets.UTF_8, StandardOpenOption.WRITE,
            StandardOpenOption.TRUNCATE_EXISTING);

        String command = "cargo key -o hir.json";
        try {
            int code = Runtime.getRuntime().exec(command, null, tmpDir.toFile()).waitFor();
            assert code == 0;
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        var hir = Files.readString(tmpDir.resolve("hir.json"), Charset.defaultCharset());
        var crate = Crate.parseJSON(hir);
        var converter = new HirConverter(services);
        var converted = converter.convertCrate(crate);
        BlockExpression body = converted.getVerificationTarget().body();
        var es = (ExpressionStatement) body.getStatements().get(0);
        return new RustyBlock(es.getExpression());
    }

    public RustyBlock readBlockWithEmptyContext(String s) throws IOException {
        return readBlock(s, createEmptyContext());
    }

    public RustyBlock readBlockWithProgramVariables(Namespace<@NonNull ProgramVariable> varNS,
            String s) throws IOException {
        return readBlock(s, new Context(varNS));
    }

    /**
     * creates an empty compilation unit with a temporary name.
     *
     * @return the new recoder.java.CompilationUnit
     */
    public Context createEmptyContext() {
        return new Context(new Namespace<>());
    }
}
