/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

/**
 * This interface defines the known property names in the project settings.
 *
 * @author AL
 */
public interface PropertyNames {

    /**
     * Property <TT>output.path</TT>.
     * <p>
     * <p>
     * Defines the output path used by the {@link recoder.io.SourceFileRepository}to write back
     * changed or new compilation units. Defaults to the corresponding environment variable or if
     * there is none, the current user directory.
     */
    String OUTPUT_PATH = "output.path";

    /**
     * Property <TT>input.path</TT>.
     * <p>
     * <p>
     * Defines the search path list used by the {@link recoder.io.ClassFileRepository}and
     * {@link recoder.io.SourceFileRepository}to load new classes. Defaults to the corresponding
     * environment variable or if there is none, the current class path, or if there is none, ".".
     * The system should at least define the java.lang-classes.
     */
    String INPUT_PATH = "input.path";

    /**
     * Property <TT>jdk1.4</TT>.
     * <p>
     * <p>
     * Defines the global behavior of the parser and lexer: If set, <CODE>
     * assert</CODE> is considered a keyword, otherwise no assert statement can be parsed. The
     * setting defaults to <CODE>true</CODE>
     */
    String JDK1_4 = "jdk1.4";

    /**
     * Property <TT>JAVA_5</TT>.
     * <p>
     * <p>
     * Defines the global behavior of the parser and lexer: If set, <CODE>
     * Java 5 language features (like generics, autoboxing, ...) are accepted.
     * Setting this property to <CODE>true</CODE> automatically sets the property <TT>JDK1_4</TT> to
     * <CODE>true</CODE>. The setting defaults to <CODE>true</CODE>
     */
    String JAVA_5 = "java5";

    /**
     * Property <TT>ADD_NEWLINE_AT_END_OF_FILE</TT>
     * <p>
     * If set to <CODE>true</CODE>, adds an extra newline at end of each source file, which allows
     * to parse files that end with a single line comment (without a newline feed). While those are
     * not valid .java-files, most compilers accept these files. The setting defaults to
     * <CODE>true</CODE>
     */
    String ADD_NEWLINE_AT_END_OF_FILE = "extra_newline_at_end_of_file";

    /**
     * Property <TT>error.threshold</TT>.
     * <p>
     * <p>
     * Defines the maximum number of errors the error handler accepts before falling back to a safe
     * state.
     */
    String ERROR_THRESHOLD = "error.threshold";

    /**
     * Property <TT>class.search.mode</TT>.
     * <p>
     * <p>
     * Defines the search mode of the {@link recoder.service.NameInfo}. Valid values consist of a
     * combination of at most one of each mode indicators <CODE>'s'</CODE>,<CODE>'c'</CODE> and
     * <CODE>'r'</CODE> (or uppercase versions). <DL COMPACT>
     * <DT><CODE>'s'</CODE>
     * <DD>look for source files
     * <DT><CODE>'c'</CODE>
     * <DD>look for class files
     * <DT><CODE>'r'</CODE>
     * <DD>look for classes by runtime reflection
     * </DL>
     * <p>
     * Examples: <BR>
     * <CODE>"sc"</CODE>- default setting, looks for source files, then class files. <BR>
     * <CODE>"scr"</CODE>- use reflection as a last resort. <BR>
     * <CODE>""</CODE>- do not reload classes at all.
     */
    String CLASS_SEARCH_MODE = "class.search.mode";

    /**
     * Property <TT>overwriteParsePositions</TT>.
     * <p>
     * <p>
     * If set, global parse positions of source elements are reset by the pretty printer according
     * to the new positions. Default is <TT>false</TT>.
     */
    String OVERWRITE_PARSE_POSITIONS = "overwriteParsePositions";

    /**
     * Property <TT>overwriteIndentation</TT>.
     * <p>
     * <p>
     * If set, indentations are always set by the pretty printer, even if they already are defined.
     * Default is <TT>false</TT>.
     */
    String OVERWRITE_INDENTATION = "overwriteIndentation";

    /**
     * Property <TT>indentationAmount</TT>.
     * <p>
     * <p>
     * The number of blanks for each indentation level. Default is 4.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=33%>n = 2</TH>
     * <TH WIDTH=33%>n = 3</TH>
     * <TH WIDTH=33%>n = 4</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * while (i < n) { if (a[i] == x) { return i; } i += 1; }
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * <p>
     * while (i < n) { if (a[i] == x) { return i; } i += 1; }
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * <p>
     * while (i < n) { if (a[i] == x) { return i; } i += 1; }
     *
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String INDENTATION_AMOUNT = "indentationAmount";

    /**
     * Property <TT>glueStatementBlocks</TT>.
     * <p>
     * <p>
     * If set, the opening bracket of a statement block follows immediately after the parent
     * instruction. Default is <TT>true</TT>.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * void foo() { ...
     * <p>
     * <p>
     * while... { ...
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * <p>
     * void foo() { ...
     * <p>
     * while... { ...
     *
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_STATEMENT_BLOCKS = "glueStatementBlocks";

    /**
     * Property <TT>glueSequentialBranches</TT>.
     * <p>
     * <p>
     * If set, branches Else, Catch, Default, Catch and Finally follows immediately after the
     * closing bracket of the previous branch or the enclosing statement. Default is <TT>true</TT>.
     * If set, the property <TT>glueStatementBlocks</TT> should also be set.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * ... } else ...
     * ' switch ... case ... case ... default ...
     * <p>
     * ... } catch ... } catch ... } finally ...
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * <p>
     * ... } else ...
     * <p>
     * switch ... case ... case ... default ...
     * <p>
     * ... } catch ... } catch ... } finally ...
     *
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_SEQUENTIAL_BRANCHES = "glueSequentialBranches";

    /**
     * Property <TT>glueControlExpressions</TT>.
     * <p>
     * <p>
     * If set, the boolean condition of a conditional statement follows immediately after the
     * statement keyword. Default is <TT>false</TT>.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * if(x > 0) ...
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * <p>
     * if (x > 0) ...
     *
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_CONTROL_EXPRESSIONS = "glueControlExpressions";

    /**
     * Property <TT>glueParameterLists</TT>.
     * <p>
     * <p>
     * If set, the parameter list of a method declaration as well as a method call and exception
     * catch clauses follows immediately after the method name or the catch symbol. Default is
     * <TT>true</TT>.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * void foo(...)
     * <p>
     * catch(...)
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * <p>
     * void foo (...)
     * <p>
     * catch (...)
     *
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_PARAMETER_LISTS = "glueParameterLists";

    /**
     * Property <TT>glueParameters</TT>.
     * <p>
     * <p>
     * If set, the parameters of a method declaration as well as the arguments of a method call
     * follows immediately after the comma. Default is <TT>
     * false</TT>.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * foo(x,y,z)
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * <p>
     * foo(x, y, z)
     *
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_PARAMETERS = "glueParameters";

    /**
     * Property <TT>glueParameterParentheses</TT>.
     * <p>
     * <p>
     * If set, the parameters of a method declaration as well as a method call follow / end
     * immediately after / before the parantheses. Default is <TT>
     * true</TT>.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * foo(x,...,z)
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * <p>
     * foo( x,...,z )
     *
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_PARAMETER_PARENTHESES = "glueParameterParentheses";

    /**
     * Property <TT>glueExpressionParentheses</TT>.
     * <p>
     * <p>
     * If set, expressions in parentheses follow / end immediately after / before the parantheses.
     * Default is <TT>true</TT>.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * (1 < < 3)
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * ( 1 < < 3 )
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_EXPRESSION_PARENTHESES = "glueExpressionParentheses";

    /**
     * Property <TT>glueInitializerParentheses</TT>.
     * <p>
     * <p>
     * If set, expressions in initializer blocks follow / end immediately after / before the
     * brackets. Default is <TT>false</TT>.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * {1, 2, 3}
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * { 1, 2, 3 }
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_INITIALIZER_PARENTHESES = "glueInitializerParentheses";

    /**
     * Property <TT>glueInfixOperators</TT>.
     * <p>
     * <p>
     * If set, infix operators are attached to their operands. Default is <TT>
     * false</TT>.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * x=y>0?a+b*c:0
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * <p>
     * x = y > 0 ? a + b * c : 0
     *
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_INFIX_OPERATORS = "glueInfixOperators";

    /**
     * Property <TT>glueUnaryOperators</TT>.
     * <p>
     * <p>
     * If set, unary operators are attached to their operands. Default is <TT>
     * true</TT>.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * -(a++)
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * -(a++)
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_UNARY_OPERATORS = "glueUnaryOperators";

    /**
     * Property <TT>glueMembers</TT>.
     * <p>
     * <p>
     * If set, members follow without blank lines in between. Default is <TT>
     * false</TT>.
     * <p>
     * <TABLE BORDER>
     * <TR>
     * <TH WIDTH=50%>true</TH>
     * <TH WIDTH=50%>false</TH>
     * </TR>
     * <TR VALIGN=top>
     * <TD>
     *
     * <PRE>
     * <p>
     * int fee = 0; void foo() { ... } int faa(int x);
     *
     * </PRE>
     *
     * </TD>
     * <TD>
     *
     * <PRE>
     * <p>
     * int fee = 0;
     * <p>
     * void foo() { ... }
     * <p>
     * int faa(int x);
     *
     * </PRE>
     *
     * </TD>
     * </TR>
     * </TABLE>
     */
    String GLUE_MEMBERS = "glueMembers";

    String GLUE_LABELS = "glueLabels";

    String ALIGN_LABELS = "alignLabels";

    String GLUE_DECLARATION_APPENDICES = "glueDeclarationAppendices";

    String INDENT_CASE_BRANCHES = "indentCaseBranches";

    String TABSIZE = "TabSize";
}
