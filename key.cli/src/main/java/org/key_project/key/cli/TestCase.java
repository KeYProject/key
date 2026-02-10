package org.key_project.key.cli;

import java.util.ArrayList;
import java.util.List;

public class TestCase {
    public String name;
    public String classname = "";
    public Integer assertions = null;
    public Integer time = null;
    public String status = null;
    public TestCaseKind result = TestCaseKind.UNKNOWN;
    public String sysout = null;
    public String syserr = null;

    public TestCase(String name) {
        this.name = name;
    }

    public boolean isDisabled() {
        return result instanceof TestCaseKind.Skipped;
    }

    public boolean hasFailures() {
        return result instanceof TestCaseKind.Failure;
    }

    public boolean hasErrors() {
        return result instanceof TestCaseKind.Error;
    }

    public void writeXml(XmlWriter writer) {
        writer.element("testcase",
                new Object[]{"name", name},
                new Object[]{"assertions", assertions},
                new Object[]{"classname", classname},
                new Object[]{"status", status},
                new Object[]{"time", time},
                () -> {
                    result.writeXml(writer);
                    if (syserr != null) {
                        writer.element("system-err", () -> writer.cdata(syserr));
                    }
                    if (sysout != null) {
                        writer.element("system-out", () -> writer.cdata(sysout));
                    }
                });
    }
}