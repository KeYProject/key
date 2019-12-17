package org.key_project.proofmanagement.io.report;

import org.key_project.proofmanagement.check.CheckResult;
import org.stringtemplate.v4.*;

import java.io.IOException;
import java.io.OutputStream;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

public class Report {
    private final CheckResult result;

    private Path outPath;

    public void setOutPath(Path outPath) {
        this.outPath = outPath;
    }

    public Report(CheckResult result) {
        this.result = result;
    }

    public String printReport() throws IOException, URISyntaxException {
        ClassLoader classLoader = getClass().getClassLoader();
        URL url = classLoader.getResource("report/");
        Path resPath = Paths.get(url.toURI());

        STGroup group = new STRawGroupDir(resPath.toString(), '$', '$');

        // STGroupFile groupFile = new STGroupFile(resPath.toString());
        //ST st = groupFile.getInstanceOf("document");
        ST st = group.getInstanceOf("report");

        st.add("title", "test report 2.0");

        st.add("text", "an arbitrary short text for testing purposes");

        String result = st.render();
        printToOutputFile(result);

        return result;
    }

    private void printToOutputFile(String str) throws IOException {
        if (outPath == null) {
            // nothing to do
            return;
        }

        Files.write(outPath, str.getBytes(StandardCharsets.UTF_8));
    }
}
