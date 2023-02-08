package de.uka.ilkd.key.proof.runallproofs;

import java.io.PrintWriter;
import java.io.Writer;

/**
 * This class allows to write test-results into XML like JUnit.
 * //https://stackoverflow.com/questions/4922867/what-is-the-junit-xml-format-specification-that-hudson-supports
 *
 * @author Alexander Weigl
 * @version 1 (8/5/20)
 */
public class JunitXmlWriter implements AutoCloseable {
    /*
     * format: <?xml version="1.0" encoding="UTF-8"?> <testsuites disabled="" errors="" failures=""
     * name="" tests="" time=""> <testsuite disabled="" errors="" failures="" hostname="" id=""
     * name="" package="" skipped="" tests="" time="" timestamp=""> <properties> <property name=""
     * value=""/> </properties> <testcase assertions="" classname="" name="" status="" time="">
     * <skipped/> <error message="" type=""/> <failure message="" type=""/> <system-out/>
     * <system-err/> </testcase> <system-out/> <system-err/> </testsuite> </testsuites>
     */

    private final PrintWriter writer;

    public JunitXmlWriter(Writer writer, String fqName, int total) {
        this.writer = new PrintWriter(writer);
        this.writer.format("<testsuites> <testsuite name=\"%s\" tests=\"%d\" id=\"0\">", fqName,
            total);
    }

    @Override
    public void close() {
        writer.format("</testsuite>");
        writer.format("</testsuites>");
        writer.flush();
        writer.close();
    }

    public void addTestcase(String name, String classname, boolean skipped, String error,
            String failure, String sout, String serr) {
        writer.format("<testcase name=\"%s\"  classname=\"%s\">", name, classname);
        if (skipped)
            writer.format("<skipped/>");

        if (error != null && !error.trim().isEmpty()) {
            writer.format("<error message=\"%s\"/>", error);
        }

        if (failure != null && !failure.trim().isEmpty()) {
            writer.format("<failure message=\"%s\"/>", error);
        }

        if (sout != null && !sout.trim().isEmpty()) {
            writer.format("<system-out><![CDATA[%s]]></system-out>", sout);
        }
        if (serr != null && !serr.trim().isEmpty()) {
            writer.format("<system-out><![CDATA[%s]]></system-out>", serr);
        }
        writer.format("</testcase>");
    }
}
