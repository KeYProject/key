/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.Comparator;

import org.key_project.logic.Namespace;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.fn.Function;
import org.key_project.rusty.ast.fn.FunctionParamPattern;
import org.key_project.rusty.ast.pat.BindingPattern;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.RustyBlock;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.parser.hir.Crate;
import org.key_project.rusty.speclang.ContractFactory;
import org.key_project.rusty.speclang.ProgramVariableCollection;
import org.key_project.util.collection.ImmutableList;

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
    public RustyBlock readBlock(String block, Context context) {
        try {
            var fn = context.buildFunction(block, true);
            {
                // TODO: remove (it's only for tests)
                fn += "pub fn my_add(a: u32, b: u32) -> u32 {a + b}";
            }
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
            System.out.println(fn);
            Files.writeString(lib, fn, StandardCharsets.UTF_8, StandardOpenOption.WRITE,
                StandardOpenOption.TRUNCATE_EXISTING);

            var command = new String[] { "cargo", "key", "-o", "hir.json" };
            try {
                Process cmd = Runtime.getRuntime().exec(command, null, tmpDir.toFile());
                var stdErr = cmd.getErrorStream();
                var errReader = new BufferedReader(new InputStreamReader(stdErr));
                var sb = new StringBuilder();
                String line;
                while ((line = errReader.readLine()) != null) {
                    sb.append(line).append("\n");
                }
                stdErr.close();
                int code = cmd.waitFor();
                // TODO: report error
                assert code == 0 : sb.toString();
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
            var hir = Files.readString(tmpDir.resolve("hir.json"), Charset.defaultCharset());
            var crate = Crate.parseJSON(hir);
            var converter = new HirConverter(services);
            var converted = converter.convertCrate(crate);
            BlockExpression body = converted.getVerificationTarget().body();
            var es = (ExpressionStatement) body.getStatements().get(0);
            {
                // TODO: remove
                var myAdd = (Function) converted.getTopMod().getItems().stream()
                        .filter(
                            i -> i instanceof Function f && f.name().toString().equals("my_add"))
                        .findFirst().orElse(null);
                assert myAdd != null;
                var target = services.getRustInfo().getFunction(myAdd);
                services.getNamespaces().functions().addSafely(target);
                var factory = new ContractFactory(services);
                var tb = services.getTermBuilder();
                var pre = tb.tt();
                var post = tb.tt();
                var a = ((BindingPattern) ((FunctionParamPattern) myAdd.params().get(0)).pattern())
                        .pv();
                var b = ((BindingPattern) ((FunctionParamPattern) myAdd.params().get(0)).pattern())
                        .pv();
                var pvs = new ProgramVariableCollection(null, ImmutableList.of(a, b), null);
                services.getSpecificationRepository().addContract(factory.func("my_contract",
                    target, true, pre, null, post, null, pvs, true));
            }
            return new RustyBlock(es.getExpression());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public RustyBlock readBlockWithEmptyContext(String s) {
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
