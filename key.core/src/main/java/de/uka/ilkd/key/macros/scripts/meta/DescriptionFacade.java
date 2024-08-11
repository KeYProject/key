/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.macros.scripts.meta;

import java.lang.reflect.Field;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

import org.key_project.util.java.StringUtil;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This facade is used to load documentation for {@link ProofScriptCommand} and
 * {@link ProofScriptArgument}.
 * <p>
 * It uses a {@code COMMANDS_DESCRIPTION} property file.
 *
 * @author Alexander Weigl
 * @version 1 (18.08.17)
 */
public final class DescriptionFacade {
    /**
     * The filename of the XML properties containing the documentation of proof script commands.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(DescriptionFacade.class);

    private static final String NO_DOCUMENTATION = "No documentation available.";
    private static final String HTML_NO_DOCUMENTATION = "<i>" + NO_DOCUMENTATION + "</i>";

    private DescriptionFacade() {
    }

    public static <T> String getHTMLDocumentation(Class<T> parameterClazz) {
        if (parameterClazz == null)
            return HTML_NO_DOCUMENTATION;

        StringBuilder sb = new StringBuilder();
        Description description = parameterClazz.getAnnotation(Description.class);

        if(description != null) {

            for (String p : StringUtil.escapeHtmlEntities(description.value()).split("\n")) {
                sb.append("<p>").append(p).append("</p>");
            }

            String[] examples = description.examples();
            if (examples.length > 0) {
                sb.append("<h2>Examples</h2>");
                sb.append("<ul>");
                for (String li : examples) {
                    sb.append("<li>").append(StringUtil.escapeHtmlEntities(li)).append("</li>");
                }
                sb.append("</ul>");
            }
        }

        boolean fields = false;
        for (Field field : parameterClazz.getDeclaredFields()) {
            Option option = field.getDeclaredAnnotation(Option.class);
            if (option != null) {
                if (!fields) {
                    sb.append("<h2>Parameters</h2>");
                    sb.append("<dl>");
                    fields = true;
                }
                sb.append("<dt>").append(option.value()).append("</dt><dd>").append(option.help()).append("</dd>");
            }
        }
        if (fields) {
            sb.append("</dl>");
        }

        if(sb.length() == 0) {
            return HTML_NO_DOCUMENTATION;
        }

        return sb.toString();
    }

    public static <T> String getDocumentation(Class<T> parameterClazz) {
        if (parameterClazz == null)
            return NO_DOCUMENTATION;

        StringBuilder sb = new StringBuilder();
        Description description = parameterClazz.getAnnotation(Description.class);

        if(description != null) {

            sb.append(description.value().replace("\n", "\n\n"));

            String[] examples = description.examples();
            if (examples.length > 0) {
                sb.append("\n\nExamples:\n");
                for (String li : examples) {
                    sb.append("    ").append(li).append("\n");
                }
            }
        }

        boolean fields = false;
        for (Field field : parameterClazz.getDeclaredFields()) {
            Option option = field.getDeclaredAnnotation(Option.class);
            if (option != null) {
                if (!fields) {
                    sb.append("\nParameters:\n");
                    fields = true;
                }
                sb.append(" > ").append(option.value()).append(" <\n    ").append(option.help()).append("\n");
            }
        }

        if(sb.length() == 0) {
            return NO_DOCUMENTATION;
        }

        return sb.toString();
    }
}
