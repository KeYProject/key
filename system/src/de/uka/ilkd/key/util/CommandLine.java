// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * A small framework to handle command lines.
 *
 * <p>
 * Command line options can be defined beforehand, the command line be parsed
 * and set options be queried. It is possible to print a short usage message.
 *
 * <p>
 * <i>Note</i> one can use {@code --} to end the list of command line options.
 * This is used if an argument bears a name of a command line option.
 *
 * <h3>Typical usage</h3>
 *
 * <pre>
 * CommandLine cl = new CommandLine();
 * cl.addOption(&quot;-help&quot;, null, &quot;Print usage&quot;);
 * cl.addOption(&quot;-noArg&quot;, null, &quot;Parameter w/o argument&quot;);
 * cl.addOption(&quot;-argument&quot;, &quot;argname&quot;, &quot;Parameter w/ argument&quot;);
 *
 * // public static void main(String[] args) :
 * cl.parse(args);
 *
 * if (cl.isSet(CMDLINE_HELP)) {
 *     cl.printUsage(System.out);
 *     System.exit(0);
 * }
 *
 * if (cl.isSet(&quot;-noArg&quot;)) {
 *     // do something
 * }
 *
 * // retrieve a set value
 * String s = cl.getString(&quot;-argument&quot;, &quot;default value if not set&quot;);
 *
 * // or retrieve a set integer value
 * // this throws a CommandLineException if not formatted as an integer
 * int intVal = cl.getInteger(&quot;-argument&quot;, 42);
 *
 * list = cl.getArguments();
 * // handle remaining arguments
 * </pre>
 *
 * @author Mattias Ulbrich (for ivil)
 */
public final class CommandLine {

    private static final String MINUS = "--";

    /**
     * Help elements are messages which can appear in usage pages, here: Options
     * and AdditionalHelpTexts.
     */
    private static abstract class HelpElement {
        protected abstract void print(PrintStream ps, int descriptionCol);
    }

    /**
     * Option is a data-only structure to capture a single cmd-line option,
     * its description as well as its value, if set.
     *
     * It carries also the information for printing the usage message.
     * Additional help text which does not belong to this option directly
     * may be referenced to by the option.
     */
    private class Option extends HelpElement {
        private String description;
        private String image;
        private String value;
        private String parameter;

        @Override
        protected void print(PrintStream stream, int descriptionCol) {
            String s = image;
            if(parameter != null) {
                s += " " + parameter;
            }

            indent(stream, indentSize);
            stream.print(s);
            indent(stream, descriptionCol - s.length());

            printIndentedMessage(stream, description,
                    descriptionCol + indentSize);
        }

    }
    /**
     * Text that should appear in usage pages. If an external help option/command 
     * with description should appear in helptext and printed similar to internal options
     */
    private class AdditionalHelpTextParts extends HelpElement {
        private String description;
        private String command;
        @SuppressWarnings("unused")
        private boolean indentToDescriptionColumn;

        @Override
        protected void print(PrintStream ps, int descriptionCol) {
            int indent = indentSize;
            
         
            indent(ps, indent);
            printIndentedMessage(ps, command, descriptionCol);
            indent(ps, descriptionCol-command.length());
            printIndentedMessage(ps, description, 0);
        }
    }
    /**
     * Text that should appear in usage pages. You can decide about the
     * indentation of the text (beginning of line or description column).
     */
    private class AdditionalHelpText extends HelpElement {
        private String description;
        private boolean indentToDescriptionColumn;

        @Override
        protected void print(PrintStream ps, int descriptionCol) {
            int indent = indentSize;
            if(indentToDescriptionColumn) {
                indent += descriptionCol;
            }
            indent(ps, indent);
            printIndentedMessage(ps, description, indent);
        }
    }
    /**
     * Prints section-headlines without any indent
     * @author sarah
     *
     */
    private class AdditionalHelpTextSection extends HelpElement {
        private String text;
        //private boolean indentToDescriptionColumn;

        @Override
        protected void print(PrintStream ps, int descriptionCol) {


            printIndentedMessage(ps, text, 0);
        }
    }
    /**
     * default value for the length of a line for output.
     */
    private static final int DEFAULT_LINE_LENGTH = 80;

    /**
     * The options that have been defined. Mapped from their image.
     */
    private final Map<String, Option> options = new LinkedHashMap<String, Option>();

    /**
     * The collected list of elements to be printed on the usage page.
     */
    private final List<HelpElement> helpElements = new ArrayList<HelpElement>();

    /**
     * The additional arguments which do not belong to an option.
     */
    private final List<String> arguments = new LinkedList<String>();

    /**
     * This is the number of characters printed in one line when printing the
     * usage page. Longer lines are broken at spaces (if possible).
     */
    private int lineLength = DEFAULT_LINE_LENGTH;

    /**
     * the number of spaces to indent the lines when printing the help
     * screen. By default lines are not indented;
     */
    private int indentSize = 0;

    /**
     * Instantiates a new command line handling object.
     */
    public CommandLine() {
    }

    /**
     * Adds a command line option to this handler.
     *
     * @param image
     *            the image of the option (e.g. {@code -help})
     * @param parameter
     *            simple description/name of the argument, null if there is no
     *            argument for this option (e.g. {@code <file>, time, path}, ...
     * @param description
     *            the description of the option
     */
    public void addOption(String image, String parameter, String description) {

        if(!image.startsWith(MINUS)) {
            throw new IllegalArgumentException("Parameters need to start with '-': " + image);
        }

        if(options.containsKey(image)) {
            throw new IllegalArgumentException(image + " has already been registered");
        }

        Option o = new Option();
        o.image = image;
        o.parameter = parameter;
        o.description = description+"\n";
        options.put(image, o);
        helpElements.add(o);
    }

    /**
     * Adds an additional help text to be printed on the usage page.
     *
     * Calling this method has no influence of the parsing of command line
     * arguments.
     *
     * @param description
     *            the text to be displayed
     * @param identToDescriptionColumn
     *            if <code>true</code>, the code is printed underneath the
     *            remaining descriptions, otherwise it has the full length.
     */
    public void addText(String description, boolean identToDescriptionColumn) {
        AdditionalHelpText text = new AdditionalHelpText();
        text.description = description;
        text.indentToDescriptionColumn = identToDescriptionColumn;
        helpElements.add(text);
    }
    /**
     * Add help text of a command which is not part of teh KeY prover, but part of the running script
     * @param command
     * @param description
     * @param identToDescriptionColumn
     */
    public void addTextPart(String command, String description, boolean identToDescriptionColumn) {
        AdditionalHelpTextParts text = new AdditionalHelpTextParts();
        text.command = command;
        text.description = description;
        text.indentToDescriptionColumn = identToDescriptionColumn;
        helpElements.add(text);
    }
    /**
     * Add Section Heading without any indentation
     * @param text
     */
    public void addSection(String text) {
        AdditionalHelpTextSection head = new AdditionalHelpTextSection();
        head.text = "\n"+text+"\n\n";

        helpElements.add(head);
    }

    /**
     * Parses the command line.
     *
     * @param args
     *                typically the array of command line arguments passed to
     *                the main method.
     *
     * @throws CommandLineException
     *                If a option is unknown or badly formatted.
     */
    public void parse(String[] args) throws CommandLineException {
        int cnt = 0;
        while (cnt < args.length && args[cnt].startsWith(MINUS)) {

            if("--".equals(args[cnt])) {
                cnt ++;
                break;
            }

            String current = args[cnt];
            Option option = options.get(current);

            if (option == null) {
                throw new CommandLineException("Unknown command line option: " + current);
            }

            if(option.parameter != null) {
                if(cnt == args.length - 1) {
                    throw new CommandLineException("Command line option " + current +
                            " expects a parameter but did not receive one");
                }
                cnt ++;
                option.value = args[cnt];
            } else {
                option.value = "true";
            }

            cnt ++;
        }

        while(cnt < args.length) {
            arguments.add(args[cnt]);
            cnt ++;
        }
    }

    /**
     * Gets the non-option arguments of the command line.
     *
     * @return a read-only list of strings.
     */
    public List<String> getArguments() {
        return Collections.unmodifiableList(arguments);
    }

    /**
     * Checks if a boolean command line option is set.
     *
     * @param param
     *                the image of the command line option to be checked
     *
     * @return true if the option is set, false otherwise
     */
    public boolean isSet(String param) {

        Option option = options.get(param);
        assert option != null : param + " is unknown option";

        return option.value != null;
    }

    /**
     * Gets the parameter string passed to an argument option.
     *
     * If the parameter has not been specified, return the default value.
     *
     * @param param
     *                the command line option. Needs to take an argument
     * @param defaultValue
     *                the default value to return if option is not set
     *
     * @return either the set option or defaultValue if not set.
     */
    public String getString(String param, String defaultValue) {
        Option option = options.get(param);
        assert option != null : param + " is unknown option";
        assert option.parameter != null : param + " does not take arguments";

        String value = option.value;
        return value == null ? defaultValue : value;
    }


    /**
     * Gets the value of an integer command line option.
     *
     * If not present, a default value is returned. If the argument cannot be
     * parsed as a (positive or negative) integer, a
     * {@link CommandLineException} is thrown.
     *
     * @param param
     *            the option to retrieve
     * @param defaultValue
     *            the default value to use if no value specified
     *
     * @return either the set option or defaultValue if not set.
     *
     * @throws CommandLineException
     *             if the argument is ill-formatted.
     */
    public int getInteger(String param, int defaultValue) throws CommandLineException {
        Option option = options.get(param);
        assert option != null : param + " is unknown option";

        String value = option.value;
        if(value == null) {
            return defaultValue;
        }

        try {
            return Integer.decode(value);
        } catch (NumberFormatException e) {
            throw new CommandLineException(param + " expects an integer argument, but received: "
                                            + option.value, e);
        }
    }

    /**
     * Gets the value of a long integer command line option.
     *
     * If not present, a default value is returned. If the argument cannot be
     * parsed as a (positive or negative) integer, a
     * {@link CommandLineException} is thrown.
     *
     * @param param
     *            the option to retrieve
     * @param defaultValue
     *            the default value to use if no value specified
     *
     * @return either the set option or defaultValue if not set.
     *
     * @throws CommandLineException
     *             if the argument is ill-formatted.
     */
    public long getLong(String param, long defaultValue) throws CommandLineException {
        Option option = options.get(param);
        assert option != null : param + " is unknown option";

        String value = option.value;
        if(value == null) {
            return defaultValue;
        }

        try {
            return Long.decode(value);
        } catch (NumberFormatException e) {
            throw new CommandLineException(param + " expects a long integer argument, but received: "
                                            + option.value, e);
        }
    }

    /**
     * Prints the usage page for this command line.
     *
     * <p>
     * Every of the page is indented to the level set by
     * {@link #setIndentation(int)} (default is 0). The options and help texts
     * appear in the order of definition (by
     * {@link #addOption(String, String, String)} and
     * {@link #addText(String, boolean)}) The descriptions of the options All
     * option descriptions commence in the same column.
     *
     * <p>
     * Descriptions which would result in lines longer than
     * {@link #getLineLength()} characters are broken at spaces (if that is
     * possible).
     *
     * @param stream
     *            the stream to print to (typically System.out)
     */
    public void printUsage(PrintStream stream) {
        int descriptionCol = 0;

        for (Option option : options.values()) {
            int len = option.image.length();
            if(option.parameter != null) {
                len += 1 + option.parameter.length();
            }
            descriptionCol = Math.max(len, descriptionCol);
        }

        descriptionCol += 2;

        for (HelpElement element : helpElements) {
            element.print(stream, descriptionCol);
        }

        stream.flush();
    }

    /*
     * insert a number of spaces to the output stream
     */
    private void indent(PrintStream stream, int len) {
        for (int i = len; i > 0; i--) {
            stream.print(" ");
        }
    }

    /*
     * Used by the Help elements to print text, potentially broken.
     * The current lines is assumed to be indented to "indentionLevel".
     * At most textWidth characters of text are printed, the line broken,
     * indented to indentationLevel, ...
     * Repeated till the text is completely rendered.
     * Output ends with a line break;
     */
    private void printIndentedMessage(PrintStream stream, String text, int indentationLevel) {
        int textWidth = getLineLength() - indentationLevel;
        while (text.length() > textWidth) {
            int p = text.lastIndexOf(' ', textWidth);

            if (p > 0) {
                stream.println(text.substring(0, p));
                text = text.substring(p + 1);
            } else {
                stream.println(text);
                text = "";
            }

            indent(stream, indentationLevel);
        }

        stream.print(text);
    }

    /**
     * Gets the indentation depth.
     *
     * This is the number of spaces which is put in front of the options when
     * printing the help screen.
     *
     * @return a non-negative number
     */
    public int getIndentation() {
        return indentSize;
    }

    /**
     * Sets the indentation depth to the argument.
     *
     * This is the number of spaces which is put in front of the options when
     * printing the usage page.
     *
     * @param indentSize
     *            a non-negative number
     */
    public void setIndentation(int indentSize) {
        this.indentSize = indentSize;
    }

    /**
     * Gets the line length used for the usage page.
     *
     * This is the number of characters printed in one line when printing the
     * usage page. Longer lines are broken at spaces (if possible).
     *
     * @return the line length
     */
    public int getLineLength() {
        return lineLength;
    }

    /**
     * Sets the line length used for the usage page.
     *
     * This is the number of characters printed in one line when printing the
     * usage page. Longer lines are broken at spaces (if possible).
     *
     * @return the line length
     */
    public void setLineLength(int lineLength) {
        this.lineLength = lineLength;
    }
}