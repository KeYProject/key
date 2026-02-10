package org.key_project.key.cli;

import java.util.ArrayList;
import java.util.Date;
import java.util.List;

public class TestSuite extends ArrayList<TestCase> {
    public String name = "";
    public String hostname = "localhost";
    public String package_ = "";
    public String timestamp = new Date().toString();
    public java.util.Map<String, Object> properties = new java.util.HashMap<>();

    public int tests() {
        return size();
    }

    public int disabled() {
        return (int) stream().filter(TestCase::isDisabled).count();
    }

    public int errors() {
        return (int) stream().filter(TestCase::hasErrors).count();
    }

    public int failures() {
        return (int) stream().filter(TestCase::hasFailures).count();
    }

    public int skipped() {
        return 0; // Placeholder
    }

    public int time() {
        return 0; // Placeholder
    }

    public void writeXml(XmlWriter writer) {
        writer.element("testsuites",
                new Object[]{"errors", errors()},
                new Object[]{"disabled", disabled()},
                new Object[]{"failures", failures()},
                new Object[]{"tests", tests()},
                new Object[]{"hostname", hostname},
                new Object[]{"package", package_},
                new Object[]{"skipped", skipped()},
                new Object[]{"timestamp", timestamp},
                new Object[]{"time", time()},
                () -> {
                    writer.element("properties", () -> {
                        for (var entry : properties.entrySet()) {
                            writer.element("property",
                                    new Object[]{"name", entry.getKey()},
                                    new Object[]{"value", entry.getValue().toString()});
                        }
                    });
                    for (TestCase testCase : this) {
                        testCase.writeXml(writer);
                    }
                });
    }

    public TestCase newTestCase(String name) {
        TestCase testCase = new TestCase(name);
        add(testCase);
        return testCase;
    }
}