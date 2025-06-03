/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;
import java.util.Objects;
import java.util.TreeMap;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.java.ast.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;
import de.uka.ilkd.key.nparser.builder.TacletPBuilder;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.parsing.BuildingException;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.sv.SchemaVariable;

import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import com.fasterxml.jackson.dataformat.yaml.YAMLGenerator;
import com.fasterxml.jackson.dataformat.yaml.YAMLMapper;
import org.antlr.v4.runtime.ParserRuleContext;
import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (13.08.23)
 */
public class SchemaJavaRegressionTest {
    Path rulesDir = Paths.get("../key.core/src/main/resources/de/uka/ilkd/key/proof/rules");

    private final Services services;

    {
        try {
            var env = KeYEnvironment
                    .load(Paths.get("../key.ui/examples/standard_key/prop_log/contraposition.key"));
            services = env.getServices();
        } catch (ProblemLoaderException e) {
            throw new RuntimeException(e);
        }
    }

    @Test
    void createOracle() throws IOException {
        var factory = YAMLFactory.builder()
                .enable(YAMLGenerator.Feature.SPLIT_LINES)
                .enable(YAMLGenerator.Feature.LITERAL_BLOCK_STYLE)
                .build();
        YAMLMapper mapper = new YAMLMapper(factory);
        try (var yaml = new FileWriter("srjt.yaml")) {
            mapper.writeValue(yaml, matchingExpressions().entrySet());
        }
    }

    Map<String, Object> matchingExpressions() throws IOException {
        Files.list(rulesDir).parallel()
                .forEach(this::extractSchemaJava);
        return modalities;
    }

    TreeMap<String, Object> modalities = new TreeMap<>();

    private void extractSchemaJava(Path it) {
        try {
            var file = ParsingFacade.parseFile(it);
            var ctx = ParsingFacade.getParseRuleContext(file);
            findModalities(ctx);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void findModalities(KeYParser.FileContext ctx) {
        var nss = services.getNamespaces();
        Namespace<SchemaVariable> schemaVariables = new Namespace<>();
        Namespace<IProgramVariable> programVariables = new Namespace<>();

        TacletPBuilder tpb = new TacletPBuilder(services, nss);
        tpb.setSchemaVariables(schemaVariables);

        class FindMods extends KeYParserBaseVisitor<Void> {
            @Override
            public Void visitOne_schema_var_decl(KeYParser.One_schema_var_declContext ctx) {
                if (ctx.PROGRAM() != null)
                    try {
                        ctx.accept(tpb);
                    } catch (BuildingException ignored) { // name clashes
                    }
                return null;
            }

            @Override
            public Void visitModality_term(KeYParser.Modality_termContext ctx) {
                final var e = ExpressionBuilder.trimJavaBlock(ctx.MODALITY().getText());
                final var cleaned = e.trim().replace('\n', ' ')
                        .replaceAll(" {2,}", " ");

                if (!modalities.containsKey(cleaned)) {
                    Object javaBlock = null;
                    for (int i = 0; i < 10; i++) {
                        try {
                            javaBlock = parseSchemaJava(ctx, e);
                            break;
                        } catch (Exception ignored) {
                            javaBlock = ignored;
                        }
                    }

                    modalities.put(Objects.requireNonNull(cleaned), javaBlock);
                }
                return null;
            }

            private Object parseSchemaJava(ParserRuleContext ctx, String cleanJava) {
                var jr = services.getJavaService();
                try {
                    return traverse(jr.readBlockWithProgramVariables(programVariables, cleanJava,
                        schemaVariables));
                } catch (Exception e) {
                    try {
                        return traverse(jr.readBlockWithEmptyContext(cleanJava, schemaVariables));
                    } catch (BuildingExceptions e1) {
                        throw new BuildingException(ctx,
                            "Could not parse java: '" + cleanJava + "'", e1);
                    }
                }
            }

            private Object traverse(JavaBlock javaBlock) {
                return traverse(javaBlock.program());
            }

            private Object traverse(JavaProgramElement program) {
                try {
                    var e = (NonTerminalProgramElement) program;
                    if (e.getChildCount() != 0) {
                        TreeMap<String, Object> map = new TreeMap<>();
                        map.put("name", program.getClass().getSimpleName());
                        for (int i = 0; i < e.getChildCount(); i++) {
                            map.put("z" + i, traverse(e.getChildAt(i)));
                        }
                        return map;
                    }
                } catch (ClassCastException ignored) {
                }

                TreeMap<String, Object> map = new TreeMap<>();
                map.put("name", program.getClass().getSimpleName());
                map.put("value", program.toString());
                return map;
            }

            private Object traverse(ProgramElement it) {
                try {
                    return traverse((JavaProgramElement) it);
                } catch (ClassCastException e) {
                    return it.toString();
                }
            }
        }
        ctx.accept(new FindMods());
    }
}
