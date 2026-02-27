/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testfixtures;

import ch.qos.logback.classic.spi.ILoggingEvent;
import ch.qos.logback.core.ConsoleAppender;
import ch.qos.logback.core.encoder.LayoutWrappingEncoder;
import ch.qos.logback.core.testUtil.StringListAppender;
import org.junit.jupiter.api.extension.AfterTestExecutionCallback;
import org.junit.jupiter.api.extension.BeforeTestExecutionCallback;
import org.junit.jupiter.api.extension.ExtensionContext;
import org.slf4j.LoggerFactory;

/**
 * Extension of JUnit 5 that suppress logging of non-failing tests.
 *
 * @author Alexander Weigl
 * @version 1 (2/17/26)
 */
public class TestLogMgr implements AfterTestExecutionCallback, BeforeTestExecutionCallback {
    private static ch.qos.logback.classic.Logger root =
        (ch.qos.logback.classic.Logger) LoggerFactory
                .getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME);

    private static final ConsoleAppender<ILoggingEvent> consoleAppender;

    private static final StringListAppender<ILoggingEvent> listAppender =
        new StringListAppender<>();

    static {
        consoleAppender = (ConsoleAppender<ILoggingEvent>) root.getAppender("STDOUT");
        listAppender.setContext(consoleAppender.getContext());
        listAppender.setLayout(
            ((LayoutWrappingEncoder<ILoggingEvent>) consoleAppender.getEncoder()).getLayout());
        listAppender.start();
    }

    @Override
    public void afterTestExecution(ExtensionContext context) {
        root.detachAppender(listAppender);
        root.addAppender(consoleAppender);
        if (context.getExecutionException().isPresent()) {
            for (var s : listAppender.strList) {
                System.out.print(s);
            }
            System.out.flush();
        }
        listAppender.strList.clear();
    }

    @Override
    public void beforeTestExecution(ExtensionContext context) {
        System.out.flush();
        root.detachAppender(consoleAppender);
        root.addAppender(listAppender);
    }
}
