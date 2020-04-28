package org.key_project.proofmanagement.io;

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

/**
 * Provides a static method to print the check results in HTML format to a given path.
 *
 * @author Wolfram Pfeifer
 */
public final class HTMLReport {
    /** to prevent from instantiating */
    private HTMLReport() {
    }

    /**
     * Prints out the given check results to a target path.
     * @param data the check results to print
     * @param target the target path of the output
     * @throws IOException if an error occurs when accessing to the target path
     * @throws URISyntaxException if the StringTemplate resources for generating the html file
     *  are not found
     */
    public static void print(CheckerData data, Path target) throws IOException, URISyntaxException {

        ST st = prepareStringTemplate();

        st.add("title", "test report 2.0");

        PathNode fileTree = data.getFileTree();

        st.add("checkerData", data);
        st.add("bundleFileName", fileTree == null ? null : fileTree.getContent());
        st.add("treeRoot", fileTree);
        st.add("entries", data.getProofEntries());
        st.add("graph", data.getDependencyGraph());

        data.print("All checks completed!");
        data.print("Generating html report ...");
        String output = st.render();
        Files.write(target, output.getBytes(StandardCharsets.UTF_8));
    }

    /**
     * Set up StringTemplate model adaptors and listeners.
     * @return the ST object for rendering the HTML report
     * @throws URISyntaxException if an error occurs accessing the StringTemplate resources
     */
    private static ST prepareStringTemplate() throws URISyntaxException {
        ClassLoader classLoader = HTMLReport.class.getClassLoader();
        URL url = classLoader.getResource("report/html/");
        Path resPath = Paths.get(url.toURI());

        STGroup group = new STRawGroupDir(resPath.toString(), '$', '$');

        // provide access to getter methods with a name equal to the property (without "get")
        // (needed to access some KeY properties, e.g. Proof.name()
        group.registerModelAdaptor(Object.class, new ObjectModelAdaptor() {
            @Override
            public synchronized Object getProperty(Interpreter interp, ST self, Object o,
                                                   Object property, String propertyName)
                    throws STNoSuchPropertyException {
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
            public Object getProperty(Interpreter interp, ST self, Object o, Object property,
                                      String propertyName)
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
                throw new RuntimeException(msg.toString(), msg.cause);
            }

            @Override
            public void runTimeError(STMessage msg) {
                throw new RuntimeException(msg.toString(), msg.cause);
            }

            @Override
            public void IOError(STMessage msg) {
                throw new RuntimeException(msg.toString(), msg.cause);
            }

            @Override
            public void internalError(STMessage msg) {
                throw new RuntimeException(msg.toString(), msg.cause);
            }
        });

        return group.getInstanceOf("report");
    }
}
