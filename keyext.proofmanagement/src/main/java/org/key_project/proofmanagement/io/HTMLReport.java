/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.io;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

import freemarker.template.DefaultObjectWrapper;
import org.key_project.proofmanagement.check.CheckerData;
import org.key_project.proofmanagement.check.PathNode;
import org.key_project.util.java.IOUtil;

import freemarker.template.Configuration;
import freemarker.template.Template;
import freemarker.template.TemplateException;

/**
 * Provides a static method to print the check results in HTML format to a given path.
 *
 * @author Wolfram Pfeifer
 */
public final class HTMLReport {
    /**
     * to prevent from instantiating
     */
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
        Configuration cfg = new Configuration(Configuration.VERSION_2_3_32);
        cfg.setClassLoaderForTemplateLoading(HTMLReport.class.getClassLoader(), "/report/html");
        cfg.setDefaultEncoding("UTF-8");

        // Use DefaultObjectWrapper to expose fields of objects in the data model
        DefaultObjectWrapper wrapper = new DefaultObjectWrapper(Configuration.VERSION_2_3_32);
        wrapper.setExposeFields(true);
        cfg.setObjectWrapper(wrapper);

        // Load template
        Template template = cfg.getTemplate("report.ftl");

        // Prepare data model
        Map<String, Object> st = new HashMap<>();

        st.put("style", loadFromClasspath("/report/html/style.css"));
        st.put("scripts", loadFromClasspath("/report/html/scripts.js"));


        st.put("title", data.getPbh() != null ? data.getPbh().getBundleName() : "");

        PathNode fileTree = data.getFileTree();

        st.put("checkerData", data);
        st.put("bundleFileName", fileTree == null ? null : fileTree.getContent());
        st.put("treeRoot", fileTree);
        st.put("entries", data.getProofEntries());
        st.put("graph", data.getDependencyGraph());

        data.print("All checks completed!");
        data.print("Generating html report ...");


        try (var out = Files.newBufferedWriter(target)) {
            template.process(st, out);
            data.print("Report generated at " + target.normalize());
        } catch (IOException e) {
            data.print("Unable to generate report: " + e.getMessage());
        } catch (TemplateException e) {
            throw new RuntimeException(e);
        }
    }

    private static String loadFromClasspath(String name) throws IOException {
        InputStream input = HTMLReport.class.getResourceAsStream(name);
        if (input == null) {
            return "";
        }
        return IOUtil.readFrom(input);
    }

}
