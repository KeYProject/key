import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import com.fasterxml.jackson.dataformat.yaml.YAMLGenerator;
import com.fasterxml.jackson.dataformat.yaml.YAMLMapper;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;
import de.uka.ilkd.key.nparser.builder.TacletPBuilder;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.junit.jupiter.api.Test;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;
import java.util.TreeMap;

/**
 * @author Alexander Weigl
 * @version 1 (13.08.23)
 */
public class SchemaJavaRegressionTest {
    Path rulesDir = Paths.get("../key.core/src/main/resources/de/uka/ilkd/key/proof/rules");

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
        Services services = new Services(JavaProfile.getDefaultProfile());
        var nss = services.getNamespaces();
        Namespace<SchemaVariable> schemaVariables = new Namespace<>();
        Namespace<IProgramVariable> programVariables = new Namespace<>();

        TacletPBuilder tpb = new TacletPBuilder(services, nss);
        tpb.setSchemaVariables(schemaVariables);

        class FindMods extends KeYParserBaseVisitor<Void> {
            @Override
            public Void visitOne_schema_var_decl(KeYParser.One_schema_var_declContext ctx) {
                if (ctx.PROGRAM() != null)
                    ctx.accept(tpb);
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
                            javaBlock = parseSchemaJava(e);
                            break;
                        } catch (Exception ignored) {
                        }
                    }

                    modalities.put(cleaned, javaBlock);
                }
                return null;
            }

            private Object parseSchemaJava(String cleanJava) {
                SchemaJavaReader jr = new SchemaRecoder2KeY(services, nss);
                jr.setSVNamespace(schemaVariables);
                try {
                    return traverse(jr.readBlockWithProgramVariables(programVariables, cleanJava));
                } catch (Exception e) {
                    return traverse(jr.readBlockWithEmptyContext(cleanJava));
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

