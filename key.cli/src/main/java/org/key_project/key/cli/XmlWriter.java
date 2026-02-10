package org.key_project.key.cli;

import java.io.IOException;
import java.io.Writer;

public class XmlWriter {
    private final Writer stream;

    public XmlWriter(Writer stream) {
        this.stream = stream;
    }

    public void write(String s) throws IOException {
        stream.write(s);
    }

    public void attr(String key, Object value) throws IOException {
        if (value != null) {
            stream.write(" " + key + " = \"" + value + "\"");
        }
    }

    public void element(String s, Object[] attrs, Runnable function) throws IOException {
        stream.write("<" + s);
        for (int i = 0; i < attrs.length; i += 2) {
            attr((String) attrs[i], attrs[i + 1]);
        }
        if (function != null) {
            function.run();
        }
        stream.write("</" + s + ">");
    }

    public void cdata(String it) throws IOException {
        stream.write("<![CDATA[");
        stream.write(it);
        stream.write("]]>");
    }
}