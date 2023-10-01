/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.io;

import java.io.IOException;
import java.lang.reflect.Method;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;

import org.key_project.proofmanagement.check.CheckerData;
import org.key_project.proofmanagement.check.PathNode;

import org.stringtemplate.v4.*;
import org.stringtemplate.v4.misc.MapModelAdaptor;
import org.stringtemplate.v4.misc.ObjectModelAdaptor;
import org.stringtemplate.v4.misc.STMessage;
import org.stringtemplate.v4.misc.STNoSuchPropertyException;

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
     *
     * @param data the check results to print
     * @param target the target path of the output
     * @throws IOException if an error occurs when accessing to the target path or the string
     *         template resources
     */
    public static void print(CheckerData data, Path target) throws IOException {

        ST st = prepareStringTemplate();

        st.add("title", data.getPbh().getBundleName() + " - Proof Management Report");

        PathNode fileTree = data.getFileTree();

        st.add("checkerData", data);
        st.add("bundleFileName", fileTree == null ? null : fileTree.getContent());
        st.add("treeRoot", fileTree);
        st.add("entries", data.getProofEntries());
        st.add("graph", data.getDependencyGraph());

        data.print("All checks completed!");
        data.print("Generating html report ...");
        try {
            String output = st.render();
            Files.write(target, output.getBytes(StandardCharsets.UTF_8));
            data.print("Report generated at " + target.normalize());
        } catch (IOException e) {
            data.print("Unable to generate report: " + e.getMessage());
        }
    }

    /**
     * Set up StringTemplate model adaptors and listeners.
     *
     * @return the ST object for rendering the HTML report
     * @throws IOException if an error occurs accessing the StringTemplate resources
     */
    private static ST prepareStringTemplate() throws IOException {
        ClassLoader classLoader = HTMLReport.class.getClassLoader();
        URL url = classLoader.getResource("report/html");

        if (url == null) {
            throw new IOException("Could not load report template resource from report/html.");
        }

        STGroup group = new STRawGroupDir(url, "UTF-8", '$', '$');

        // provide access to getter methods with a name equal to the property (without "get")
        // (needed to access some KeY properties, e.g. Proof.name()
        group.registerModelAdaptor(Object.class, new ObjectModelAdaptor<>() {
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
        Class<Map<?, ?>> mapClass = (Class<Map<?, ?>>) (Class) Map.class;
        group.registerModelAdaptor(mapClass, new MapModelAdaptor() {
            @Override
            public Object getProperty(Interpreter interp, ST self, Map<?, ?> map, Object property,
                    String propertyName)
                    throws STNoSuchPropertyException {
                if (property.equals("entrySet")) {
                    return map.entrySet();
                }
                return super.getProperty(interp, self, map, property, propertyName);
            }
        });

        /*
         * This additional ModelAdaptor is workaround needed for access of Node.getValue in string
         * template, otherwise we would have to add this to build.gradle files in key.ui and
         * keyext.proofmanagement:
         * jvmArgs += ['--add-opens', 'java.base/java.util=ALL-UNNAMED']
         */
        Class<Map.Entry<?, ?>> mapEntryClass = (Class<Map.Entry<?, ?>>) (Class) Map.Entry.class;
        group.registerModelAdaptor(mapEntryClass, new ObjectModelAdaptor<>() {
            @Override
            public synchronized Object getProperty(Interpreter interp, ST self,
                    Map.Entry<?, ?> entry, Object property,
                    String propertyName)
                    throws STNoSuchPropertyException {
                if (property.equals("value")) {
                    return entry.getValue();
                } else if (property.equals("key")) {
                    return entry.getKey();
                }
                return super.getProperty(interp, self, entry, property, propertyName);
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
