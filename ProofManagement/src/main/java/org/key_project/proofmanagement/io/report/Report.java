package org.key_project.proofmanagement.io.report;

import org.key_project.proofmanagement.check.CheckerData;
import org.key_project.proofmanagement.check.PathNode;
import org.stringtemplate.v4.*;
import org.stringtemplate.v4.misc.ObjectModelAdaptor;
import org.stringtemplate.v4.misc.STMessage;
import org.stringtemplate.v4.misc.STNoSuchPropertyException;
import sun.util.resources.cldr.zh.CalendarData_zh_Hans_HK;

import java.io.IOException;
import java.lang.reflect.Method;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;

public class Report {
    private final CheckerData result;

    private Path outPath;

    public void setOutPath(Path outPath) {
        this.outPath = outPath;
    }

    public Report(CheckerData result) {
        this.result = result;
    }

    public String printReport() throws IOException, URISyntaxException {
        ClassLoader classLoader = getClass().getClassLoader();
        URL url = classLoader.getResource("report/");
        Path resPath = Paths.get(url.toURI());

        STGroup group = new STRawGroupDir(resPath.toString(), '$', '$');
        group.registerModelAdaptor(Object.class, new ObjectModelAdaptor() {
            @Override
            public synchronized Object getProperty(Interpreter interp, ST self, Object o, Object property, String propertyName) throws STNoSuchPropertyException {
                Method m = tryGetMethod(o.getClass(), propertyName);
                if (m != null) {
                    try {
                        Object resilt = m.invoke(o);
                        System.out.println(resilt);
                        return resilt;
                    } catch (Exception e) {
                        throwNoSuchProperty(o.getClass(), propertyName, e);
                    }
                }

                return super.getProperty(interp, self, o, property, propertyName);
            }
        });

        // STGroupFile groupFile = new STGroupFile(resPath.toString());
        //ST st = groupFile.getInstanceOf("document");
        ST st = group.getInstanceOf("report");
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

        st.add("title", "test report 2.0");

        PathNode fileTree = result.getFileTree();

        st.add("bundleFileName", fileTree == null ? null : fileTree.content);
        st.add("treeRoot", fileTree == null ? null : fileTree);
        st.add("lines", result.getProofLines());
        st.add("graph", result.getDependencyGraph());

        String output = st.render();
        printToOutputFile(output);

        return output;
    }

    private void printToOutputFile(String str) throws IOException {
        if (outPath == null) {
            // nothing to do
            return;
        }

        Files.write(outPath, str.getBytes(StandardCharsets.UTF_8));
    }
}
