/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// package de.uka.ilkd.key.gui.sourceview;
//
// import de.uka.ilkd.key.gui.colors.ColorSettings;
// import de.uka.ilkd.key.nparser.KeYLexer;
// import de.uka.ilkd.key.parser.proofjava.JavaCharStream;
// import de.uka.ilkd.key.parser.proofjava.ProofJavaParser;
// import de.uka.ilkd.key.parser.proofjava.ProofJavaParserTokenManager;
// import static de.uka.ilkd.key.parser.proofjava.ProofJavaParserConstants.*;
//
// import de.uka.ilkd.key.parser.proofjava.Token;
// import de.uka.ilkd.key.speclang.njml.JmlLexer;
// import org.antlr.v4.runtime.CharStreams;
//
// import javax.swing.text.SimpleAttributeSet;
// import javax.swing.text.StyleConstants;
// import java.awt.*;
// import java.io.StringReader;
// import java.util.ArrayList;
// import java.util.BitSet;
// import java.util.List;
//
// public class JMLEditorLexer implements SourceHighlightDocument.EditorLexer {
//
// /** highight color for Java keywords (dark red/violet) */
// private static final ColorSettings.ColorProperty JAVA_KEYWORD_COLOR =
// ColorSettings.define("[java]keyword", "", new Color(0x7f0055));
//
// // private static final Color JAVA_STRING_COLOR = new Color(0x000000);
//
// /** highight color for comments (dull green) */
// private static final ColorSettings.ColorProperty COMMENT_COLOR =
// ColorSettings.define("[java]comment", "", new Color(0x3f7f5f));
//
// /** highight color for JavaDoc (dull green) */
// private static final ColorSettings.ColorProperty JAVADOC_COLOR =
// ColorSettings.define("[java]javadoc", "", new Color(0x3f7f5f));
//
// /** highight color for JML (dark blue) */
// private static final ColorSettings.ColorProperty JML_COLOR =
// ColorSettings.define("[java]jml", "", new Color(0x0000c0));
//
// /** highight color for JML keywords (blue) */
// private static final ColorSettings.ColorProperty JML_KEYWORD_COLOR =
// ColorSettings.define("[java]jmlKeyword", "", new Color(0x0000f0));
//
//
// /** default style */
// private static final SimpleAttributeSet normal = new SimpleAttributeSet();
//
// /** the style of keywords */
// private static final SimpleAttributeSet keyword = new SimpleAttributeSet();
//
// /** the style of comments and line comments */
// private static final SimpleAttributeSet comment = new SimpleAttributeSet();
//
// /** the style of JavaDoc */
// private static final SimpleAttributeSet javadoc = new SimpleAttributeSet();
//
// /** the style of JML annotations */
// private static final SimpleAttributeSet jml = new SimpleAttributeSet();
//
// /** the style of JML keywords */
// private static final SimpleAttributeSet jmlkeyword = new SimpleAttributeSet();
//
// private static final BitSet KEYWORDS = new BitSet();
// private static final BitSet JAVDOCS = new BitSet();
// private static final BitSet COMMENTS = new BitSet();
// private static final BitSet JMLS = new BitSet();
// private static final BitSet JMLKEYWORDS = new BitSet();
//
// static {
// StyleConstants.setBold(keyword, true);
// StyleConstants.setForeground(keyword, JAVA_KEYWORD_COLOR.get());
// StyleConstants.setForeground(comment, COMMENT_COLOR.get());
// StyleConstants.setForeground(javadoc, JAVADOC_COLOR.get());
// // StyleConstants.setForeground(string, JAVA_STRING_COLOR);
// StyleConstants.setForeground(jml, JML_COLOR.get());
// StyleConstants.setForeground(jmlkeyword, JML_KEYWORD_COLOR.get());
// StyleConstants.setBold(jmlkeyword, true);
// addAll(KEYWORDS, ABSTRACT, ASSERT, BOOLEAN, BREAK, BYTE, CASE, CATCH, CHAR, CLASS, CONST,
// CONTINUE, DEFAULT,
// DO, DOUBLE, ELSE, ENUM, EXTENDS, FINAL, FINALLY, FLOAT, FOR, GOTO, IF, IMPLEMENTS, IMPORT,
// INSTANCEOF,
// INT, INTERFACE, LONG, NATIVE, NEW, PACKAGE, PRIVATE, PROTECTED, PUBLIC, RETURN, SHORT, STATIC,
// STRICTFP,
// SUPER, SWITCH, SYNCHRONIZED, THIS, THROW, THROWS, TRANSIENT, TRY, VOID, VOLATILE, WHILE);
//// addAll(LITERALS, STRING_LITERAL, HEX_LITERAL, INT_LITERAL, FLOAT_LITERAL, DOUBLE_LITERAL,
// REAL_LITERAL, TRUE,
//// FALSE);
// addAll(COMMENTS, SINGLE_LINE_COMMENT, MULTI_LINE_COMMENT);
// addAll(JAVDOCS, FORMAL_COMMENT);
// }
//
// private static void addAll(BitSet bitSet, int... values) {
// for (int value : values) {
// bitSet.set(value);
// }
// }
//
// private SimpleAttributeSet getAttributes(int kind) {
// if(KEYWORDS.get(kind)) {
// return keyword;
// } else if(COMMENTS.get(kind)) {
// return comment;
// } else if(JAVDOCS.get(kind)) {
// return javadoc;
// } else {
// return normal;
// }
// }
//
// private SimpleAttributeSet getJMLAttributes(int kind) {
// if(kind == JmlLexer.ENSURES) {
// return jmlkeyword;
// } else {
// return jml;
// }
// }
//
// @Override
// public List<SourceHighlightDocument.Token> applyTo(String text) {
// ProofJavaParser.initialize(new StringReader(text));
// ProofJavaParserTokenManager tm = ProofJavaParser.token_source;
// List<SourceHighlightDocument.Token> result = new ArrayList<>();
// Token t = tm.getNextToken();
// while(t.kind != 0) {
// System.out.println(t.kind + " " + t.image);
// if(t.kind == SINGLE_LINE_COMMENT && t.image.startsWith("//@") ||
// t.kind == MULTI_LINE_COMMENT && t.image.startsWith("/*@")) {
// result.addAll(parseJML(t.image));
// } else {
// result.add(new SourceHighlightDocument.Token(t.image.length(), getAttributes(t.kind)));
// }
//
// if (t.specialToken != null) {
// t = t.specialToken;
// } if (t.next != null) {
// t = t.next;
// } else {
// t = tm.getNextToken();
// }
// }
// return result;
// }
//
// private List<SourceHighlightDocument.Token> parseJML(String text) {
// JmlLexer jmlLexer = new JmlLexer(CharStreams.fromString(text));
// List<SourceHighlightDocument.Token> result = new ArrayList<>();
// var t = jmlLexer.nextToken();
// while(t.getType() != -1) {
// result.add(new SourceHighlightDocument.Token(t.getText().length(),
// getJMLAttributes(t.getType())));
// t = jmlLexer.nextToken();
// }
// return result;
// }
// }
