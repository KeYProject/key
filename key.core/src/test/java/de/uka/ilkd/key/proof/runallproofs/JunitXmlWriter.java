/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;

import java.io.PrintWriter;
import java.io.Writer;
import java.util.*;

/**
 * This class allows to write test-results into XML like JUnit.
 * https://stackoverflow.com/questions/4922867/what-is-the-junit-xml-format-specification-that-hudson-supports
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

    private final Writer writer;
    private final String suiteName;
    private final List<TestCase> testcases = new ArrayList<>(16);

    public JunitXmlWriter(Writer writer, String fqName) {
        this.writer = writer;
        suiteName = fqName;
    }

    @Override
    public void close() {
        try (var p = new PrintWriter(writer)) {
            var total = testcases.size();
            long disabled =
                testcases.stream().filter(it -> it.state == TestCaseState.SKIPPED).count();
            long errors = testcases.stream().filter(it -> it.state == TestCaseState.ERROR).count();
            long failures =
                testcases.stream().filter(it -> it.state == TestCaseState.FAILED).count();
            double time = testcases.stream().mapToDouble(it -> it.time).sum();

            p.format(
                "<testsuites> <testsuite name=\"%s\" tests=\"%d\" id=\"0\" disabled=\"%d\" errors=\"%d\" failures=\"%d\" time=\"%f\">",
                suiteName, total, disabled, errors, failures, time);

            for (var tc : testcases) {
                p.format("<testcase name=\"%s\"  classname=\"%s\" time=\"%f\">", tc.name,
                    tc.classname, tc.time);
                if (tc.state == TestCaseState.SKIPPED)
                    p.format("<skipped/>");

                if (tc.error != null && !tc.error.trim().isEmpty()) {
                    p.format("<error message=\"%s\"/>", tc.error);
                }

                if (tc.failure != null && !tc.failure.trim().isEmpty()) {
                    p.format("<failure message=\"%s\"/>", tc.error);
                }

                if (tc.sout != null && !tc.sout.trim().isEmpty()) {
                    p.format("<system-out><![CDATA[%s]]></system-out>", tc.sout);
                }
                if (tc.serr != null && !tc.serr.trim().isEmpty()) {
                    p.format("<system-out><![CDATA[%s]]></system-out>", tc.serr);
                }
                p.format("</testcase>");
            }

            p.format("</testsuite>");
            p.format("</testsuites>");
        }
    }

    public void addTestcase(
            String name,
            String classname,
            TestCaseState state,
            String error,
            String failure,
            String sout,
            String serr,
            double time) {
        testcases.add(
            new TestCase(state, name, suiteName + "." + classname, error, failure, sout, serr,
                time));
    }

    enum TestCaseState {
        FAILED,
        ERROR,
        SUCCESS,
        SKIPPED
    }

    private static class TestCase {

        final String name, classname, error, failure, sout, serr;
        final TestCaseState state;
        final double time;

        public TestCase(
                TestCaseState state,
                String name,
                String classname,
                String error,
                String failure,
                String sout,
                String serr,
                double time) {
            this.name = name;
            this.classname = classname;
            this.state = state;
            this.error = error;
            this.failure = failure;
            this.sout = sout;
            this.serr = serr;
            this.time = time;
        }
    }
}
