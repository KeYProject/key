package org.key_project.key.cli;

public abstract class TestCaseKind {
    public abstract void writeXml(XmlWriter writer);

    public static class UNKNOWN extends TestCaseKind {
        @Override
        public void writeXml(XmlWriter writer) {
            // No-op
        }
    }

    public static class Skipped extends TestCaseKind {
        public String message;

        public Skipped(String message) {
            this.message = message;
        }

        @Override
        public void writeXml(XmlWriter writer) {
            writer.element("skipped", new Object[]{"message", message});
        }
    }

    public static class Error extends TestCaseKind {
        public String message;
        public String type;

        public Error(String message, String type) {
            this.message = message;
            this.type = type;
        }

        @Override
        public void writeXml(XmlWriter writer) {
            writer.element("error", new Object[]{"message", message}, new Object[]{"type", type});
        }
    }

    public static class Failure extends TestCaseKind {
        public String message;
        public String type = "";

        public Failure(String message, String type) {
            this.message = message;
            this.type = type;
        }

        @Override
        public void writeXml(XmlWriter writer) {
            writer.element("failure", new Object[]{"message", message});
        }
    }
}