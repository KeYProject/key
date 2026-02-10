package org.key_project.key.cli;

import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

public class TestSuites extends ArrayList<TestSuite> {
    public String name = "";

    public int tests() {
        return stream().mapToInt(TestSuite::tests).sum();
    }

    public int disabled() {
        return stream().mapToInt(TestSuite::disabled).sum();
    }

    public int errors() {
        return stream().mapToInt(TestSuite::errors).sum();
    }

    public int failures() {
        return stream().mapToInt(TestSuite::failures).sum();
    }

    public int time() {
        return stream().mapToInt(TestSuite::time).sum();
    }

    public void writeXml(Writer writer) {
        try (var xmlWriter = new XmlWriter(writer)) {
            writeXml(xmlWriter);
        } catch (Exception e) {
            Ansi.err("Failed to write XML: " + e.getMessage());
        }
    }

    public void writeXml(XmlWriter writer) {
        writer.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
        writer.element("testsuites",
                new Object[]{"errors", errors()},
                new Object[]{"disabled", disabled()},
                new Object[]{"failures", failures()},
                new Object[]{"tests", tests()},
                new Object[]{"time", time()},
                () -> {
                    for (TestSuite suite : this) {
                        suite.writeXml(writer);
                    }
                });
    }

    public TestSuite newTestSuite(String name) {
        TestSuite suite = new TestSuite();
        suite.name = name;
        add(suite);
        return suite;
    }
}