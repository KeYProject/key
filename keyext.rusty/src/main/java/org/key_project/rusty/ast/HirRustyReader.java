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

import org.key_project.logic.Name;
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
import org.key_project.rusty.proof.init.ContractPO;
import org.key_project.rusty.proof.init.InitConfig;
import org.key_project.rusty.proof.init.ProofInputException;
import org.key_project.rusty.speclang.ContractFactory;
import org.key_project.rusty.speclang.FunctionalOperationContract;
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

            var wrapperOutput = getWrapperOutput(tmpDir);
            var converter = new HirConverter(services, null);
            var converted = converter.convertCrate(wrapperOutput.crate());
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
                if (services.getNamespaces().functions().lookup(target.name()) == null) {
                    services.getNamespaces().functions().add(target);
                    var factory = new ContractFactory(services);
                    var tb = services.getTermBuilder();
                    var a =
                        ((BindingPattern) ((FunctionParamPattern) myAdd.params().get(0)).pattern())
                                .pv();
                    var b =
                        ((BindingPattern) ((FunctionParamPattern) myAdd.params().get(1)).pattern())
                                .pv();
                    var result = new ProgramVariable(new Name("result"), a.getKeYRustyType());
                    var pre = tb.geq(tb.var(a), tb.zero());
                    var post = tb.equals(tb.var(result), tb.add(tb.var(a), tb.var(b)));
                    var pvs = new ProgramVariableCollection(null, ImmutableList.of(a, b), result);
                    FunctionalOperationContract contract = factory.func("my_contract",
                        target, true, pre, null, post, null, pvs, true);
                    services.getSpecificationRepository().addContract(contract);
                    ContractPO proofObl = contract.createProofObl(new InitConfig(services));
                    proofObl.readProblem();
                    System.out.println(proofObl.getPO().getProof(0).getOpenGoals()
                            .head().getNode().sequent());
                }
            }
            return new RustyBlock(es.getExpression());
        } catch (IOException e) {
            throw new RuntimeException(e);
        } catch (ProofInputException e) {
            throw new RuntimeException(e);
        }
    }

    public static Crate.WrapperOutput getWrapperOutput(Path path) throws IOException {
        return getWrapperOutput(path, false);
    }

    public static Crate.WrapperOutput getWrapperOutput(Path path, boolean clean)
            throws IOException {
        try {
            Process cleanCmd =
                Runtime.getRuntime().exec(new String[] { "cargo", "clean" }, null, path.toFile());
            cleanCmd.waitFor();
            var command = new String[] { "cargo", "key", "-o", "hir.json" };
            Process cmd = Runtime.getRuntime().exec(command, null, path.toFile());
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
        var hir = Files.readString(path.resolve("hir.json"), Charset.defaultCharset());
        var wrapperOutput = Crate.parseJSON(hir);
        return wrapperOutput;
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
