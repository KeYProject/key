package org.key_project.proofmanagement.io.report;

import org.key_project.proofmanagement.check.CheckerData;
import org.key_project.proofmanagement.check.PathNode;
import org.stringtemplate.v4.Interpreter;
import org.stringtemplate.v4.NumberRenderer;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STErrorListener;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STRawGroupDir;
import org.stringtemplate.v4.StringRenderer;
import org.stringtemplate.v4.misc.MapModelAdaptor;
import org.stringtemplate.v4.misc.ObjectModelAdaptor;
import org.stringtemplate.v4.misc.STMessage;
import org.stringtemplate.v4.misc.STNoSuchPropertyException;

import java.io.IOException;
import java.lang.reflect.Method;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;

public class Report {
    private final CheckerDataView dataView;
    private Path outPath;

    public void setOutPath(Path outPath) {
        this.outPath = outPath;
    }

    public Report(CheckerData result) {
        this.dataView = new CheckerDataView(result);
    }

    public String printReport() throws IOException, URISyntaxException {
        ClassLoader classLoader = getClass().getClassLoader();
        URL url = classLoader.getResource("report/");
        Path resPath = Paths.get(url.toURI());

        STGroup group = new STRawGroupDir(resPath.toString(), '$', '$');

        // provide access to getter methods with a name equal to the property (without "get")
        group.registerModelAdaptor(Object.class, new ObjectModelAdaptor() {
            @Override
            public synchronized Object getProperty(Interpreter interp, ST self, Object o, Object property, String propertyName) throws STNoSuchPropertyException {
                Method m = tryGetMethod(o.getClass(), propertyName);
                if (m != null) {
                    try {
                        return m.invoke(o);
                    } catch (Exception e) {
                        throwNoSuchProperty(o.getClass(), propertyName, e);
                    }
                }
                return super.getProperty(interp, self, o, property, propertyName);
            }
        });

        // provide access to entrySet property of Maps
        group.registerModelAdaptor(Map.class, new MapModelAdaptor() {
            @Override
            public Object getProperty(Interpreter interp, ST self, Object o, Object property, String propertyName)
                    throws STNoSuchPropertyException {
                Map<?, ?> map = (Map<?, ?>) o;
                if (property.equals("entrySet")) {
                    return map.entrySet();
                }
                return super.getProperty(interp, self, o, property, propertyName);
            }
        });

        // StringRenderer to escape special HTML chars, for example in java.lang.Object::<inv>
        group.registerRenderer(String.class, new StringRenderer());
        // NumberRenderer to allow for format strings such as %02d
        group.registerRenderer(Number.class, new NumberRenderer());

        // register listeners to get error output on console
        group.setListener(new STErrorListener() {
            @Override
            public void compileTimeError(STMessage msg) {
                throw new RuntimeException(msg.cause);
            }

            @Override
            public void runTimeError(STMessage msg) {
                throw new RuntimeException(msg.toString(), msg.cause);
            }

            @Override
            public void IOError(STMessage msg) {
                throw new RuntimeException(msg.cause);
            }

            @Override
            public void internalError(STMessage msg) {
                throw new RuntimeException(msg.cause);
            }
        });

        ST st = group.getInstanceOf("report");
        st.add("title", "test report 2.0");

        PathNode fileTree = dataView.getFileTree();

        st.add("checkerData", dataView.getCheckerData());
        st.add("bundleFileName", fileTree == null ? null : fileTree.getContent());
        st.add("treeRoot", fileTree);
        st.add("dataView", dataView);
        st.add("lines", dataView.getProofLines());
        st.add("graph", dataView.getDependencyGraph());

        dataView.getCheckerData().print("All checks completed!");
        dataView.getCheckerData().print("Generating html report ...");
        String output = st.render();
        printToOutputFile(output);

        return output;
    }

    private void printToOutputFile(String str) throws IOException {
        if (outPath == null) {
            return;     // nothing to do
        }
        Files.write(outPath, str.getBytes(StandardCharsets.UTF_8));
    }
}
