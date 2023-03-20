/**
 * Copyright (C) 2016, The logback-contrib developers. All rights reserved.
 * <p>
 * This program and the accompanying materials are dual-licensed under
 * either the terms of the Eclipse Public License v1.0 as published by
 * the Eclipse Foundation
 * <p>
 * or (per the licensee's choosing)
 * <p>
 * under the terms of the GNU Lesser General Public License version 2.1
 * as published by the Free Software Foundation.
 */
package de.uka.ilkd.key.logging;

import ch.qos.logback.classic.pattern.*;
import ch.qos.logback.classic.spi.ILoggingEvent;
import ch.qos.logback.core.LayoutBase;

import java.io.PrintWriter;
import java.io.StringWriter;

/**
 * <code><pre>
 * {
 *   "instant" : {
 *     "epochSecond" : 1493121664,
 *     "nanoOfSecond" : 118000000
 *   },
 *   "thread" : "main",
 *   "level" : "INFO",
 *   "loggerName" : "HelloWorld",
 *   "marker" : {
 *     "name" : "child",
 *     "parents" : [ {
 *       "name" : "parent",
 *       "parents" : [ {
 *         "name" : "grandparent"
 *       } ]
 *     } ]
 *   },
 *   "message" : "Hello, world!",
 *   "thrown" : {
 *     "commonElementCount" : 0,
 *     "message" : "error message",
 *     "name" : "java.lang.RuntimeException",
 *     "extendedStackTrace" : [ {
 *       "class" : "logtest.Main",
 *       "method" : "main",
 *       "file" : "Main.java",
 *       "line" : 29,
 *       "exact" : true,
 *       "location" : "classes/",
 *       "version" : "?"
 *     } ]
 *   },
 *   "contextStack" : [ "one", "two" ],
 *   "endOfBatch" : false,
 *   "loggerFqcn" : "org.apache.logging.log4j.spi.AbstractLogger",
 *   "contextMap" : {
 *     "bar" : "BAR",
 *     "foo" : "FOO"
 *   },
 *   "threadId" : 1,
 *   "threadPriority" : 5,
 *   "source" : {
 *     "class" : "logtest.Main",
 *     "method" : "main",
 *     "file" : "Main.java",
 *     "line" : 29
 *   }
 * }
 * </pre></code>
 */
public class JsonLayout extends LayoutBase<ILoggingEvent> {
    private static final ClassOfCallerConverter ccc = new ClassOfCallerConverter();
    private static final MethodOfCallerConverter mcc = new MethodOfCallerConverter();
    private static final LineOfCallerConverter lcc = new LineOfCallerConverter();
    private static final FileOfCallerConverter fcc = new FileOfCallerConverter();

    @Override
    public String doLayout(ILoggingEvent event) {
        var sw = new StringWriter();
        var pw = new PrintWriter(sw);
        pw.print("{");
        pw.format("\"instant\": { \"epochSecond\" : %d, \"nanoOfSecond\" : 0 },",
            event.getTimeStamp());
        printEntry(pw, "thread", event.getThreadName());
        printEntry(pw, "level", event.getLevel().levelStr);
        printEntry(pw, "loggerName", event.getLoggerName());
        printEntry(pw, "message", event.getFormattedMessage()
                .replace("\\", "\\\\")
                .replace("\"", "\\\"")
                .replace("\n", "\\n"));
        if (event.getThrowableProxy() != null) {
            pw.format(
                " \"thrown\" : { \"commonElementCount\" : 0, \"message\" : \"%s\", \"name\" : \"%s\","
                    +
                    "    \"extendedStackTrace\" : [",
                event.getThrowableProxy().getMessage(),
                event.getThrowableProxy().getClassName());

            final var stackTraceElementProxyArray =
                event.getThrowableProxy().getStackTraceElementProxyArray();
            for (int i = 0; i < stackTraceElementProxyArray.length; i++) {
                var s = stackTraceElementProxyArray[i];
                pw.format(
                    "{\"class\" : \"%s\", \"method\" : \"%s\", \"file\" : \"%s\", \"line\" : %d, \"exact\": %s, \"version\":\"%s\"}",
                    s.getStackTraceElement().getClassName(),
                    s.getStackTraceElement().getMethodName(),
                    s.getStackTraceElement().getFileName(),
                    s.getStackTraceElement().getLineNumber(),
                    s.getClassPackagingData().isExact(),
                    s.getClassPackagingData().getVersion());
                if (i + 1 != stackTraceElementProxyArray.length) {
                    pw.format(", ");
                }
            }

        }
        pw.format(
            "\"source\" : { \"class\" : \"%s\", \"method\" : \"%s\", \"file\" : \"%s\", \"line\" : %s}",
            ccc.convert(event), mcc.convert(event), fcc.convert(event), lcc.convert(event));
        pw.print("}");
        pw.println();
        return sw.toString();
    }

    private static void printEntry(PrintWriter pw, String key, Object m) {
        pw.format("\"%s\":", key);
        if (m instanceof String)
            pw.format("\"%s\",", m);
        else
            pw.format("%s,", m);
    }
}
