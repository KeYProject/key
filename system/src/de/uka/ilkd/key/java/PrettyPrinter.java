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

package de.uka.ilkd.key.java;

import java.io.IOException;
import java.io.Writer;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.ClassInitializer;
import de.uka.ilkd.key.java.declaration.ConstructorDeclaration;
import de.uka.ilkd.key.java.declaration.Extends;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.Implements;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.Throws;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.declaration.modifier.Final;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.BigintLiteral;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.DoubleLiteral;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.expression.literal.EmptySetLiteral;
import de.uka.ilkd.key.java.expression.literal.FloatLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.literal.LongLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.expression.operator.BinaryAnd;
import de.uka.ilkd.key.java.expression.operator.BinaryAndAssignment;
import de.uka.ilkd.key.java.expression.operator.BinaryNot;
import de.uka.ilkd.key.java.expression.operator.BinaryOr;
import de.uka.ilkd.key.java.expression.operator.BinaryOrAssignment;
import de.uka.ilkd.key.java.expression.operator.BinaryXOr;
import de.uka.ilkd.key.java.expression.operator.BinaryXOrAssignment;
import de.uka.ilkd.key.java.expression.operator.Conditional;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.DLEmbeddedExpression;
import de.uka.ilkd.key.java.expression.operator.Divide;
import de.uka.ilkd.key.java.expression.operator.DivideAssignment;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.ExactInstanceof;
import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.expression.operator.LogicalAnd;
import de.uka.ilkd.key.java.expression.operator.LogicalNot;
import de.uka.ilkd.key.java.expression.operator.LogicalOr;
import de.uka.ilkd.key.java.expression.operator.Minus;
import de.uka.ilkd.key.java.expression.operator.MinusAssignment;
import de.uka.ilkd.key.java.expression.operator.Modulo;
import de.uka.ilkd.key.java.expression.operator.ModuloAssignment;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.expression.operator.NotEquals;
import de.uka.ilkd.key.java.expression.operator.Plus;
import de.uka.ilkd.key.java.expression.operator.PlusAssignment;
import de.uka.ilkd.key.java.expression.operator.Positive;
import de.uka.ilkd.key.java.expression.operator.PostDecrement;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.java.expression.operator.PreDecrement;
import de.uka.ilkd.key.java.expression.operator.PreIncrement;
import de.uka.ilkd.key.java.expression.operator.ShiftLeft;
import de.uka.ilkd.key.java.expression.operator.ShiftLeftAssignment;
import de.uka.ilkd.key.java.expression.operator.ShiftRight;
import de.uka.ilkd.key.java.expression.operator.ShiftRightAssignment;
import de.uka.ilkd.key.java.expression.operator.Times;
import de.uka.ilkd.key.java.expression.operator.TimesAssignment;
import de.uka.ilkd.key.java.expression.operator.TypeCast;
import de.uka.ilkd.key.java.expression.operator.UnsignedShiftRight;
import de.uka.ilkd.key.java.expression.operator.UnsignedShiftRightAssignment;
import de.uka.ilkd.key.java.expression.operator.adt.SeqGet;
import de.uka.ilkd.key.java.expression.operator.adt.SeqLength;
import de.uka.ilkd.key.java.reference.ArrayLengthReference;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MetaClassReference;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.reference.SchemaTypeReference;
import de.uka.ilkd.key.java.reference.SuperConstructorReference;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisConstructorReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Assert;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Case;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.Default;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.Finally;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.IForUpdates;
import de.uka.ilkd.key.java.statement.ILoopInit;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.java.statement.Switch;
import de.uka.ilkd.key.java.statement.SynchronizedBlock;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.statement.TransactionStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.util.Debug;

/**
   A configurable pretty printer for Java source elements originally from COMPOST.

   @author AL
   
   CHANGED FOR KeY. Comments are not printed!
 */
public class PrettyPrinter {

    /**
       Line number, not directly used.
    */
    private int line = 0;

    /**
       Column number. Used to keep track of indentations.
    */
    private int column = 0;

    /**
       Level.
    */
    protected int level = 0;
    protected Writer out;
    protected StringBuffer outBuf;
    protected boolean noLinefeed=false;
    protected boolean noSemicolons=false;
    /**Enforces the output of real Java syntax that can be compiled. See also {@link de.uka.ilkd.key.unittest.ppAndJavaASTExtension.CompilableJavaCardPP}*/
     
    protected Type classToPrint = null;

    protected int firstStatementStart = -1;
    protected int firstStatementEnd = -1;
    protected boolean startAlreadyMarked = false;
    protected boolean endAlreadyMarked = false;
    protected Object firstStatement = null;
    protected SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;

    /** creates a new PrettyPrinter */
    public PrettyPrinter(Writer o) {
	setWriter(o);
	outBuf = new StringBuffer();
    }

    public PrettyPrinter(Writer o, SVInstantiations svi) {
    	this(o);
    	this.instantiations = svi;
    }

    public PrettyPrinter(Writer o, boolean noLinefeed) {
        this(o);
        this.noLinefeed = noLinefeed;
    }

    public PrettyPrinter(Writer o, boolean noLinefeed, SVInstantiations svi) {
        this(o, noLinefeed);
        this.instantiations = svi;
    }
    
    
    /** The number of charcters that have been send to the writer */
    protected int writtenCharacters = 0; 

    protected void output() throws IOException {
	if (noSemicolons) removeChar(outBuf, ';');
	if (noLinefeed) removeChar(outBuf, '\n');
	String toWrite = outBuf.toString();
	writtenCharacters += toWrite.length();
	out.write(toWrite);
	outBuf=new StringBuffer();
	
    }

    /** Numbers of generated characters */
    protected int getCurrentPos(){
	return writtenCharacters + outBuf.length();
    }

    /**
     * Marks the start of the first executable statement ...
     * @param n offset from the current position
     * @param stmt current statement;
     */
    protected void markStart(int n, Object stmt){
        if (!startAlreadyMarked) {

            // System.err.println("Mark start ... called");

            firstStatementStart = getCurrentPos() + n;
            firstStatement = stmt;
            startAlreadyMarked = true;
        }
    }

    /**
     * Marks the end of the first executable statement ...
     * @param n offset from the current position
     */
    protected void markEnd(int n, Object stmt){
	if (!endAlreadyMarked && (firstStatement == stmt)) {
	    
	    //  System.err.println("Mark end ... called ");
							
	    firstStatementEnd = getCurrentPos() + n;
	    endAlreadyMarked = true;
	}
    }

    /**
     * @return the range of the first executable statement that means
     * the corresponding start and end position in the string representation
     */
    public Range getRangeOfFirstExecutableStatement(){
	return new Range(firstStatementStart,firstStatementEnd);
    }

    /**
     * Resets the state of this pretty printer ...
     */
    public void reset(){
	firstStatementStart = -1;
	firstStatementEnd = -1;
	firstStatement = null;
	startAlreadyMarked = false;
	endAlreadyMarked = false;
	writtenCharacters = 0;
	outBuf = new StringBuffer();
    }
    

    /**
       Flag to indicate if a single line comment is being put out.
       Needed to disable the worklist meanwhile.
    */
    private boolean isPrintingSingleLineComments = false;


    protected HashMap<SourceElement, Position> indentMap=new LinkedHashMap<SourceElement, Position>();

    /**
       Set a new stream to write to. Useful to redirect the output
       while retaining all other settings. Resets the current source
       positions and comments.
    */
    public void setWriter(Writer out) {
        this.out = out;
        column = 0;
        line = 0;
    }

    /**
       Get current line number.
       @return the line number, starting with 0.
    */
    public int getLine() {
        return line;
    }

    /**
       Get current column number.
       @return the column number, starting with 0.
    */
    public int getColumn() {
        return column;
    }

    /**
       Get indentation level.
       @return the int value.
    */
    public int getIndentationLevel() {
        return level;
    }

    /**
       Set indentation level.
       @param level an int value.
    */
    public void setIndentationLevel(int level) {
        this.level = level;
    }

    /**
       Get total indentation.
       @return the int value.
    */
    public int getTotalIndentation() {
        return indentation * level;
    }

    /**
       Change level.
       @param delta an int value.
    */
    public void changeLevel(int delta) {
        level += delta;
    }

    private static final char[] BLANKS = new char[128];

    private static final char[] FEEDS = new char[8];

    static {
        for (int i = 0; i < FEEDS.length; i++) {
            FEEDS[i] = '\n';
        }
        for (int i = 0; i < BLANKS.length; i++) {
            BLANKS[i] = ' ';
        }
    }

    /**
       Convenience method to write indentation chars.
    */
    protected void writeIndentation(int lf, int blanks) throws IOException {
	if (!noLinefeed) {
	    if (lf > 0) {
		do {
		    int n = Math.min(lf, FEEDS.length);
		    write(FEEDS, 0, n);
		    lf -= n;
		} while (lf > 0);
	    }
	    while (blanks > 0) {
		int n = Math.min(blanks, BLANKS.length);
		write(BLANKS, 0, n);
		blanks -= n;
	    }	
	}
    }

    /**
       Convenience method to write indentation chars.
    */
    protected void writeIndentation(Position relative) throws IOException {
        writeIndentation(relative.getLine(), relative.getColumn());
    }

    /**
       Write indentation.
       @param elem a source element.
       @exception IOException occasionally thrown.
    */
    protected void writeIndentation(SourceElement elem) throws IOException {
        writeIndentation(getRelativePosition(elem.getFirstElement()));
    }

    /**
       Write internal indentation.
       @param elem a source element.
       @exception IOException occasionally thrown.
    */
    protected void writeInternalIndentation(SourceElement elem) throws IOException {
        writeIndentation(getRelativePosition(elem));
    }


    /**
       Write symbol.
       @param lf an int value.
       @param levelChange an int value.
       @param symbol a string.
       @exception IOException occasionally thrown.
    */
    protected void writeSymbol(int lf, int levelChange, String symbol) throws IOException {
        level += levelChange;
        writeIndentation(lf, getTotalIndentation());
        write(symbol);
    }

    /**
       Replace all unicode characters above ?
       by their explicit representation.
       @param str the input string.
       @return the encoded string.
    */
    protected static String encodeUnicodeChars(String str) {
        int len = str.length();
        StringBuilder buf = new StringBuilder(len + 4);
        for (int i = 0; i < len; i += 1) {
            char c = str.charAt(i);
            if (c >= 0x0100) {
                if (c < 0x1000) {
                    buf.append("\\u0").append(Integer.toString(c, 16));
                } else {
                    buf.append("\\u").append(Integer.toString(c, 16));
                }
            } else {
                buf.append(c);
            }
        }
        return buf.toString();
    }

    /**
       Store the given comment until the next line feed is written.
       @param slc the comment to delay.
     */
    protected void scheduleComment(SingleLineComment slc) {
    }

    /**
       Adds indentation for a program element if necessary and if required,
       but does not print the indentation itself.       
    */
    protected void writeElement(int lf, int levelChange, int blanks, 
				SourceElement elem) throws IOException {
        level += levelChange;
        if (lf > 0) {
            blanks += getTotalIndentation();
        }
        SourceElement first = elem.getFirstElement();
        Position indent = getRelativePosition(first);
        if (indent == Position.UNDEFINED) {
            indent = new Position(lf, blanks);
        } else {
            if (lf > indent.getLine()) { 
                indent = new Position(lf, indent.getColumn());
            }
            if (blanks > indent.getColumn()) {  
                indent = new Position(indent.getLine(), blanks);
            }
        }
        indentMap.put(first, indent);
        elem.prettyPrint(this);
    }

    protected Position getRelativePosition(SourceElement first) {
        try {
            if (indentMap.containsKey(first)) {
                return indentMap.get(first);
            } else {
                if (first!=null) return first.getRelativePosition();

            }
        } finally {
            return Position.UNDEFINED;
        }
    }

    /**
       Writes an implicit terminal token of a NonTerminal, including
       its indentation. Sets the indentation if it is necessary or
       required.
       @see SourceElement#prettyPrint
    */    
    protected void writeToken(int lf, int blanks, String image,
			      NonTerminalProgramElement parent)
        throws IOException {
        if (lf > 0) {
            blanks += getTotalIndentation();
        }
        Position indent = getRelativePosition(parent);
        if (indent == Position.UNDEFINED) {
            indent = new Position(lf, blanks);
        } else {
            if (lf > indent.getLine()) {
                indent=new Position(lf, indent.getColumn());
            }
            if (blanks > indent.getColumn()) {
                indent=new Position(indent.getLine(), blanks);
            }
        }
	indentMap.put(parent.getFirstElement(), indent); //needed ?????
        writeIndentation(indent);
        //	if (overwriteParsePositions) {
        //	    parent.setInternalParsedLine(line);
        //	    parent.setInternalParsedColumn(column);
        //	}
        write(image);
    }

    protected final void writeToken(int blanks, String image,
                                 NonTerminalProgramElement parent)
        throws IOException {
        writeToken(0, blanks, image, parent);
    }

    protected final void writeToken(String image, NonTerminalProgramElement parent)
        throws IOException {
        writeToken(0, 0, image, parent);
    }

    /**
       Write a source element.
       @param lf an int value.
       @param blanks an int value.
       @param elem a source element.
       @exception IOException occasionally thrown.
    */
    protected void writeElement(int lf, int blanks, SourceElement elem) throws IOException {
        writeElement(lf, 0, blanks, elem);
    }

    /**
       Write source element.
       @param blanks an int value.
       @param elem a source element.
       @exception IOException occasionally thrown.
    */
    protected void writeElement(int blanks, SourceElement elem) throws IOException {
        writeElement(0, 0, blanks, elem);
    }

    /**
       Write source element.
       @param elem a source element.
       @exception IOException occasionally thrown.
	*/
    protected void writeElement(SourceElement elem) throws IOException {
        writeElement(0, 0, 0, elem);
    }

    /**
       Write a complete ArrayOf<ProgramElement>.
    */
    protected void writeImmutableArrayOfProgramElement(int firstLF,
                                        int levelChange,
                                        int firstBlanks,
                                        String separationSymbol,
                                        int separationLF,
                                        int separationBlanks,
                                        ImmutableArray<? extends ProgramElement> list)
        throws IOException {
        int s = list.size();
        if (s == 0) {
            return;
        }
        writeElement(firstLF, levelChange, firstBlanks,
                            list.get(0));
        for (int i = 1; i < s; i += 1) {
            write(separationSymbol);
            writeElement(separationLF, separationBlanks,
                                list.get(i));
        }
    }

    /**
       Write a complete ArrayOf<ProgramElement> using "Keyword" style.
    */
    protected void writeKeywordList(int firstLF, int levelChange, int firstBlanks, 
				    ImmutableArray<? extends ProgramElement> list) throws IOException {
        writeImmutableArrayOfProgramElement(firstLF, levelChange, firstBlanks, "", 0, 1, list);
    }

    /**
       Write keyword list.
       @param list a program element list.
       @exception IOException occasionally thrown.
    */
    protected void writeKeywordList(ImmutableArray<? extends ProgramElement> list) throws IOException {
        writeImmutableArrayOfProgramElement(0, 0, 0, "", 0, 1, list);
    }

    /**
       Write a complete ArrayOf<ProgramElement> using "Comma" style.
    */
    protected void writeCommaList(int firstLF, int levelChange, int firstBlanks, 
				  ImmutableArray<? extends ProgramElement> list) throws IOException {
        writeImmutableArrayOfProgramElement(firstLF, levelChange, 
				   firstBlanks, ",", 0, 1, list);
    }

    /**
       Write comma list.
       @param list a program element list.
       @exception IOException occasionally thrown.
    */
    protected void writeCommaList(int separationBlanks, ImmutableArray<? extends ProgramElement> list)
        throws IOException {
        writeImmutableArrayOfProgramElement(0, 0, 0, ",", 0, separationBlanks, list);
    }

    /**
       Write comma list.
       @param list a program element list.
       @exception IOException occasionally thrown.
    */
    protected void writeCommaList(ImmutableArray<? extends ProgramElement> list) throws IOException {
        writeImmutableArrayOfProgramElement(0, 0, 0, ",", 0, 1, list);
    }

    /**
       Write a complete ArrayOf<ProgramElement> using "Line" style.
    */
    protected void writeLineList(int firstLF, int levelChange, int firstBlanks, 
				 ImmutableArray<? extends ProgramElement> list) throws IOException {
        writeImmutableArrayOfProgramElement(firstLF, levelChange, firstBlanks, "", 1, 0, list);
    }

    /**
       Write line list.
       @param list a program element list.
       @exception IOException occasionally thrown.
    */
    protected void writeLineList(ImmutableArray<? extends ProgramElement> list) throws IOException {
        writeImmutableArrayOfProgramElement(0, 0, 0, "", 1, 0, list);
    }

    /**
       Write a complete ArrayOf<ProgramElement> using "Block" style.
    */
    protected void writeBlockList(int firstLF, int levelChange, int firstBlanks, 
				  ImmutableArray<? extends ProgramElement> list) throws IOException {
        writeImmutableArrayOfProgramElement(firstLF, levelChange, firstBlanks, "", 2, 0, list);
    }

    /**
       Write block list.
       @param list a program element list.
       @exception IOException occasionally thrown.
    */
    protected void writeBlockList(ImmutableArray<? extends ProgramElement> list) throws IOException {
        writeImmutableArrayOfProgramElement(0, 0, 0, "", 2, 0, list);
    }

    private void dumpComments() throws IOException {
    }

    /**
       Write.
       @param c an int value.
       @exception IOException occasionally thrown.
    */
    public void write(int c) throws IOException {
        if (c == '\n') {
            if (!isPrintingSingleLineComments) {
                dumpComments();
            }
            column = 0;
            line += 1;
        } else {
            column += 1;
        }
        outBuf.append(c);
    }

    /**
       Write.
       @param cbuf a char value.
       @exception IOException occasionally thrown.
    */
    public void write(char[] cbuf) throws IOException {
        write(cbuf, 0, cbuf.length);
    }

    /**
       Write.
       @param cbuf an array of char.
       @param off an int value.
       @param len an int value.
       @exception IOException occasionally thrown.
    */
    public void write(char[] cbuf, int off, int len) throws IOException {
        boolean col = false;

        for (int i = off + len - 1; i >= off; i -= 1) {
            if (cbuf[i] == '\n') {
                if (!isPrintingSingleLineComments) {
                    dumpComments();
                }
                line += 1;
                if (!col) {
                    column = (off + len - 1 - i);
                    col = true;
                }
            }
        }
        if (!col) {
            column += len;
	    /*
	      int i;
	      for (i = off + len - 1; (i >= off && cbuf[i] != '\n'); i -= 1) ;
	      column = (i >= off) ? (off + len - 1 - i) : (column + len);
	    */
        }
        outBuf.append(cbuf, off, len);
    }

    /**
       Write.
       @param str a string.
       @exception IOException occasionally thrown.
    */
    public void write(String str) throws IOException {
        int i = str.lastIndexOf('\n');
        if (i >= 0) {
            column = str.length() - i + 1;
            do {
                dumpComments();
                line += 1;
                i = str.lastIndexOf('\n', i - 1);
            } while (i >= 0);
        } else {
            column += str.length();
        }
        outBuf.append(str);
    }

    /**
       Write.
       @param str a string.
       @param off an int value.
       @param len an int value.
       @exception IOException occasionally thrown.
    */
    public void write(String str, int off, int len) throws IOException {
        write(str.substring(off, off + len));
    }


    /**
       Indentation (cached).
    */
    private int indentation=2;

    /*
       Wrap threshold (cached).
       private int wrap;
    */

    /**
       Overwrite indentation flag (cached).
    */
    private boolean overwriteIndentation;

    /**
       Overwrite parse positions flag (cached).
     */
    private boolean overwriteParsePositions;
    

    /**
       Get indentation amount (blanks per level).
       @return the value of getIntegerProperty("indentationAmount").
    */
    protected int getIndentation() {
        return indentation;
    }

    /**
       Returns true if the pretty printer should also reformat existing
       code. 
       @return the value of the overwriteIndentation property.
    */
    protected boolean isOverwritingIndentation() {
        return overwriteIndentation;
    }

    /**
       Returns true if the pretty printer should reset the parse positions
       accordingly.
       @return the value of the overwriteParsePositions property.
    */
    protected boolean isOverwritingParsePositions() {
        return overwriteParsePositions;
    }

    /**
       Print program element header.
       @param lf an int value.
       @param blanks an int value.
       @param elem a program element.
       @exception IOException occasionally thrown.
    */
    protected void printHeader(int lf, int blanks, ProgramElement elem) 
	throws IOException {
	
        printHeader(lf, 0, blanks, elem);
    }

    /**
       Print program element header.
       @param blanks an int value.
       @param elem a program element.
       @exception IOException occasionally thrown.
    */
    protected void printHeader(int blanks, ProgramElement elem) throws IOException {
        printHeader(0, 0, blanks, elem);
    }

    /**
       Print program element header.
       @param elem a program element.
       @exception IOException occasionally thrown.
    */
    protected void printHeader(ProgramElement elem) throws IOException {
        printHeader(0, 0, 0, elem);
    }


    /**
       Print program element header.
       @param lf number of line feeds.
       @param levelChange the level change.
       @param blanks number of white spaces.
       @param x the program element.
       @exception IOException occasionally thrown.
    */
    protected void printHeader(int lf, int levelChange, int blanks, ProgramElement x)
	throws IOException {

        level += levelChange;
        if (lf > 0) {
            blanks += getTotalIndentation();
        }
        SourceElement first = x.getFirstElement();
        Position indent = getRelativePosition(first);
        if (indent == Position.UNDEFINED) {
            indent = new Position(lf, blanks);
        } else {
	    if (lf > indent.getLine()) {
                indent=new Position(lf, indent.getColumn());
            }
            if (blanks > indent.getColumn()) {
                indent=new Position(indent.getLine(), blanks);
            }
        }
        indentMap.put(first, indent);
    }


    /**
       Print program element footer.
       @param x the program element.
       @exception IOException occasionally thrown.
    */
    protected void printFooter(ProgramElement x) throws IOException {
	output();
    }


    protected void printOperator(Operator x, String symbol) 
    throws java.io.IOException {

        // Mark statement start ...
        markStart(0,x);


        ImmutableArray<Expression> children = x.getArguments();
        if (children != null) {
//          boolean addParentheses = x.isToBeParenthesized();
//          if (addParentheses) {
//          write('(');
//          }  //????

            if (!noLinefeed) {
                writeSymbol(1,0, "");
            }
            output();

            boolean wasNoSemicolons = noSemicolons;
            boolean wasNoLinefeed   = noLinefeed;
            noSemicolons = true;
            //	    noLinefeed=true;
            switch (x.getArity()) {
            case 2:
                noLinefeed=true;
                writeElement(0, children.get(0));
                writeToken(0, symbol, x);
                output();
                writeElement(0, children.get(1));
                break;
            case 1:
                switch (x.getNotation()) {
                case Operator.PREFIX:
                    noLinefeed = true;
                    writeToken(symbol, x);
                    writeElement(0, children.get(0));
                    output();
                    break;
                case Operator.POSTFIX:
                    noLinefeed = true;
                    writeElement(0, children.get(0));
                    writeToken(1, symbol, x);
                    break;
                default:
                    break;
                }
            }
            output();
            noSemicolons = wasNoSemicolons;
            noLinefeed   = wasNoLinefeed;
            //           if (addParentheses) {
            //    write(')');
            // }   //???? as above
            if (x instanceof Assignment) {
                // 		if (((Assignment)x).getStatementContainer() != null) {
                write(";");    //????


                // 		}
            }
            output();
            // Mark statement end ...
            markEnd(0,x);

            /*if (!noLinefeed) {
    		writeSymbol(1,0, "");
            }*/          
        }
    }

    
    public void printProgramElementName(ProgramElementName x)
	throws java.io.IOException {
	
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getProgramName());
        printFooter(x);
    }

    public void printProgramVariable(ProgramVariable x)
	    throws java.io.IOException {

	printHeader(x);
	writeInternalIndentation(x);

	write(x.name().toString());
	printFooter(x);
    }
    
    public void printProgramMethod(IProgramMethod x)
	throws java.io.IOException {

        printHeader(x);
        writeInternalIndentation(x);
        write(x.getMethodDeclaration().getProgramElementName().toString());
        printFooter(x);
    }

    public void printProgramMetaConstruct(ProgramTransformer x)
	throws java.io.IOException {
        printHeader(x);
        write(x.name().toString());
        writeToken("(", x);
    	boolean oldNoLinefeed = noLinefeed;
    	noLinefeed = true;
        if (x.getChildAt(0) != null) {
            writeElement(1, +1, 0, x.getChildAt(0));
            writeSymbol(1, -1, ")");
        } else {
            write(")");
        }
    	noLinefeed = oldNoLinefeed;
        printFooter(x);
    }

    public void printContextStatementBlock(ContextStatementBlock x)
	throws java.io.IOException {
        printHeader(x);
        
        if (x.getStatementCount() > 0) {
        	writeToken("{ .. ", x);
        	writeLineList(1, +1, 0, x.getBody());           
        	writeSymbol(1, -1, " ... }");           
        } else {
        	markStart(0, x);
        	writeToken("{ .. ", x);
            write(" ... }");           
            markEnd(0,x);        	
        }
        printFooter(x);
    }

    public void printIntLiteral(IntLiteral x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getValue());
        printFooter(x);
    }
    


    public void printBigintLiteral(BigintLiteral x) throws IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getValue());
        printFooter(x);
    }

    public void printBooleanLiteral(BooleanLiteral x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getValue() ? "true" : "false");
        printFooter(x);
    }
    
    public void printEmptySetLiteral(EmptySetLiteral x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write("\\empty");
        printFooter(x);
    }
    
    public void printSingleton(de.uka.ilkd.key.java.expression.operator.adt.Singleton x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\singleton", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(")");
        printFooter(x);
    } 
    
    public void printSetUnion(de.uka.ilkd.key.java.expression.operator.adt.SetUnion x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\set_union", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));                
        write(")");
        printFooter(x);
    }
    
    public void printIntersect(de.uka.ilkd.key.java.expression.operator.Intersect x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\intersect", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));                
        write(")");
        printFooter(x);
    }    

    public void printSetMinus(de.uka.ilkd.key.java.expression.operator.adt.SetMinus x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\set_minus", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));                
        write(")");
        printFooter(x);
    }
    
    
    public void printAllFields(de.uka.ilkd.key.java.expression.operator.adt.AllFields x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\all_fields", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(")");
        printFooter(x);
    }

    public void printAllObjects(de.uka.ilkd.key.java.expression.operator.adt.AllObjects x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\all_objects", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(")");
        printFooter(x);
    }

    public void printEmptySeqLiteral(EmptySeqLiteral x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write("\\seq_empty");
        printFooter(x);
    }
    
    public void printSeqLength(SeqLength x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeElement(0, x.getChildAt(0));
        write(".length");
        printFooter(x);
    }
    
    public void printSeqGet(SeqGet x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeElement(0, x.getChildAt(0));
        write("[");
        writeElement(1, x.getChildAt(1));
        write("]");
        printFooter(x);
    }
    
    public void printSeqSingleton(de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\seq_singleton", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(")");
        printFooter(x);
    } 
    
    public void printSeqConcat(de.uka.ilkd.key.java.expression.operator.adt.SeqConcat x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\seq_concat", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));
        write(")");
        printFooter(x);
    }    

    public void printIndexOf(de.uka.ilkd.key.java.expression.operator.adt.SeqIndexOf x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\indexOf", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));
        write(")");
        printFooter(x);
    }    
    
    public void printSeqSub(de.uka.ilkd.key.java.expression.operator.adt.SeqSub x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\seq_sub", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(",");
        writeElement(0, x.getChildAt(1));
        write(",");
        writeElement(0, x.getChildAt(2));
        write(")");
        printFooter(x);
    }  
    
    public void printSeqReverse(de.uka.ilkd.key.java.expression.operator.adt.SeqReverse x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\seq_reverse", x);
        write("(");
        writeElement(0, x.getChildAt(0));
        write(")");
        printFooter(x);
    }          
    
    public void printDLEmbeddedExpression(
            DLEmbeddedExpression x) throws IOException {
        printHeader(x);
        writeInternalIndentation(x);
        writeToken(0, "\\dl_" + x.getFunctionSymbol().name(), x);
        write("(");
        for (int i = 0; i < x.getChildCount(); i++) {
            if(i != 0) {
                write(",");
            }
            writeElement(0, x.getChildAt(i));
        }
        write(")");
        printFooter(x); 
    } 

    public void printStringLiteral(StringLiteral x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write(encodeUnicodeChars(x.getValue()));
        printFooter(x);
    }

    public void printNullLiteral(NullLiteral x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write("null");
        printFooter(x);
    }

    public void printCharLiteral(CharLiteral x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write(encodeUnicodeChars(x.getValue()));
        printFooter(x);
    }

    public void printDoubleLiteral(DoubleLiteral x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getValue());
        printFooter(x);
    }

    public void printLongLiteral(LongLiteral x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getValue());
        printFooter(x);
    }

    public void printFloatLiteral(FloatLiteral x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getValue());
        printFooter(x);
    }

    public void printPackageSpecification(PackageSpecification x) 
	throws java.io.IOException {

        printHeader(x);
        writeInternalIndentation(x);
        write("package");
        writeElement(1, x.getPackageReference());
        write(";");
        printFooter(x);
    }
    
    public void printAssert(Assert x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);

        // Mark statement start ...
        markStart(0,x);
       
        boolean wasNoLinefeed  = noLinefeed;
        boolean wasNoSemicolon = noSemicolons;

        write("assert ");        

        noLinefeed   = true;
        noSemicolons = true;
        writeElement(0, x.getCondition());
        
        if (x.getMessage() != null) {
            write(" : ");        
            writeElement(0, x.getMessage());
        }                

        noSemicolons = wasNoSemicolon;
        noLinefeed   = wasNoLinefeed;       
        
        write(";"); 

        output();
        // Mark statement end ...
        markEnd(0,x);
        
        printFooter(x);
    }
 
    public void printArrayDeclaration(ArrayDeclaration type) throws java.io.IOException {
	Type baseType = type.getBaseType().getKeYJavaType().getJavaType();       
        assert baseType != null;
	if (baseType instanceof ArrayDeclaration) {
	    printArrayDeclaration((ArrayDeclaration)baseType);
	} else {
	    writeSymbol(1, 0, baseType.getFullName());
	}
	write("[]");
    }

    public void printTypeReference(TypeReference x) throws java.io.IOException {
       printTypeReference(x, false);
    }

    public void printTypeReference(TypeReference x, boolean fullTypeNames) throws java.io.IOException {
	if (x.getKeYJavaType().getJavaType() instanceof ArrayDeclaration) {
	    printArrayDeclaration
		((ArrayDeclaration)x.getKeYJavaType().getJavaType());
	} else if (x.getProgramElementName() != null) {
	    printHeader(x);
	    if (x.getReferencePrefix() != null) {
		write(x.getReferencePrefix() + "." + x.getProgramElementName());//XXX
//		writeElement(x.getReferencePrefix());
//		writeToken(".", x);
	    } else {
	       if (fullTypeNames) {
	          write(x.getKeYJavaType().getFullName());
	       }
	       else {
	          writeElement(x.getProgramElementName());
	       }
	    }
            printFooter(x);            
        }
    }

    public void printSchemaTypeReference(SchemaTypeReference x) throws java.io.IOException {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            boolean wasNoSemicolons = noSemicolons;
            noSemicolons = true;
            writeElement(x.getReferencePrefix());
            noSemicolons = wasNoSemicolons;
            writeToken(".", x);
        }

	if (x.getProgramElementName() != null) {
            writeElement(x.getProgramElementName());
        }
        printFooter(x);
    }


    public void printFieldReference(FieldReference x) throws java.io.IOException {
        printHeader(x);
        if (x.getName()!=null && 
                "javax.realtime.MemoryArea::currentMemoryArea".
                equals(x.getName())){
            write("<currentMemoryArea>");
        } else {
            if (x.getReferencePrefix() != null) {     
                boolean wasNoSemicolons = noSemicolons;
                noSemicolons = true;
                writeElement(x.getReferencePrefix());
                noSemicolons = wasNoSemicolons;
                writeToken(".", x);
            }
            if (x.getProgramElementName() != null) {
                writeElement(x.getProgramElementName());
            }
        }
        printFooter(x);
    }

    public void printPackageReference(PackageReference x) throws java.io.IOException {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            writeToken(".", x);
        }
        if (x.getProgramElementName() != null) {
            writeElement(x.getProgramElementName());
        }
        printFooter(x);
    }

    

    public void printThrows(Throws x) throws java.io.IOException {
        printHeader(x);
        if (x.getExceptions() != null) {
            writeInternalIndentation(x);
            write("throws");	    
            
	    writeCommaList(0, 0, 1, x.getExceptions());
        }
        printFooter(x);
    }

    public void printArrayInitializer(ArrayInitializer x) 
	throws java.io.IOException {

        printHeader(x);
        writeToken("{", x);
        if (x.getArguments() != null) {
            writeCommaList(0, 0, 1, x.getArguments());
        }
        if (x.getArguments() != null && x.getArguments().size() > 0 
	    && getRelativePosition(x).getLine() > 0) {

            writeSymbol(1, 0, "}");
        } else {
            write(" }");
        }
        printFooter(x);
    }

    public void printCompilationUnit(CompilationUnit x) throws java.io.IOException {
        printHeader(x);
        setIndentationLevel(0);
        boolean hasPackageSpec = (x.getPackageSpecification() != null);
        if (hasPackageSpec) {
            writeElement(x.getPackageSpecification());
        }
        boolean hasImports = (x.getImports() != null) && (x.getImports().size() > 0);
        if (hasImports) {
            writeLineList((x.getPackageSpecification() != null) ? 2 : 0,
			  0, 0, x.getImports());
        }
        if (x.getDeclarations() != null) {
            writeBlockList((hasImports || hasPackageSpec) ? 2 : 0, 0, 0,
			   x.getDeclarations());
        }
        printFooter(x);
        // we do this linefeed here to allow flushing of the pretty printer
        // single line comment work list
        writeIndentation(1, 0);
    }

    public void printClassDeclaration(ClassDeclaration x) 
	throws java.io.IOException {
        printHeader(x);
        int m = 0;
        if (x.getModifiers() != null) {
            m = x.getModifiers().size();
        }
        if (m > 0) {
	    ImmutableArray<Modifier> mods = x.getModifiers();
            writeKeywordList(mods);
            m = 1;
        }
        if (x.getProgramElementName() != null) {
            writeToken(m, "class", x);
            writeElement(1, x.getProgramElementName());
        }
        if (x.getExtendedTypes() != null) {
            writeElement(1, x.getExtendedTypes());
        }
        if (x.getImplementedTypes() != null) {
            writeElement(1, x.getImplementedTypes());
        }
        if (x.getProgramElementName() != null) {
            write(" {");
        } else { // anonymous class
            write("{");
        }
        if (x.getMembers() != null) {
//	    services.getJavaInfo().getKeYProgModelInfo().getConstructors(kjt)
            writeBlockList(2, 1, 0, x.getMembers());
        }
        writeSymbol(1, (x.getMembers() != null) ? -1 : 0, "}");
        printFooter(x);
    }

    protected boolean containsDefaultConstructor(ImmutableArray<MemberDeclaration> members){
	for(int i=0; i<members.size(); i++){
	    MemberDeclaration md = members.get(i);
	    if(md instanceof IProgramMethod){
		md = ((IProgramMethod) md).getMethodDeclaration();
	    }
	    if((md instanceof ConstructorDeclaration) && 
	       ((ConstructorDeclaration) md).
	       getParameterDeclarationCount() == 0){
		return true;
	    }
	}
	return false;
    }

    public void printInterfaceDeclaration(InterfaceDeclaration x) 
       throws java.io.IOException {

        printHeader(x);
        int m = 0;
        if (x.getModifiers() != null) {
            m = x.getModifiers().size();
        }
        if (m > 0) {
            writeKeywordList(x.getModifiers());
            m = 1;
        }
        if (x.getProgramElementName() != null) {
            writeToken(m, "interface", x);
            writeElement(1, x.getProgramElementName());
        }
        if (x.getExtendedTypes() != null) {
            writeElement(1, x.getExtendedTypes());
        }
        write(" {");
        if (x.getMembers() != null) {
            writeBlockList(2, 1, 0, x.getMembers());
        }
        writeSymbol(1, (x.getMembers() != null) ? -1 : 0, "}");
        printFooter(x);
    }

    protected ImmutableArray<Modifier> removeFinal(ImmutableArray<Modifier> ma){
	LinkedList<Modifier> l = new LinkedList<Modifier>();
	for (Modifier mod : ma){
	    if (!(mod instanceof Final)) {
		l.add(mod);
	    }
	}
	return new ImmutableArray<Modifier>(l);
    }

    protected ImmutableArray<Modifier> replacePrivateByPublic(ImmutableArray<Modifier> ma){
	LinkedList<Modifier> l = new LinkedList<Modifier>();
	boolean publicFound = false;
	for(int i=0; i<ma.size(); i++){
	    if(ma.get(i) instanceof Private){
		l.add(new Public());
		publicFound = true;
	    }else if(ma.get(i) instanceof Public){
		l.add(ma.get(i));
		publicFound = true;
	    }else if(ma.get(i) instanceof Protected){
		l.add(new Public());
		publicFound = true;
	    }else{
		l.add(ma.get(i));
	    }
	}
	if(!publicFound){
	    l.add(new Public());
	}
	return new ImmutableArray<Modifier>(l);
    }

    public void printFieldDeclaration(FieldDeclaration x)
	    throws java.io.IOException {
	printHeader(x);
	int m = 0;
	if (x.getModifiers() != null) {
	    ImmutableArray<Modifier> mods = x.getModifiers();
	    m = mods.size();
	    writeKeywordList(mods);
	}
	writeElement((m > 0) ? 1 : 0, x.getTypeReference());
	final ImmutableArray<? extends VariableSpecification> varSpecs = x
	        .getVariables();
	assert varSpecs != null : "Strange: a field declaration without a"
	        + " variable specification";
	writeCommaList(0, 0, 1, varSpecs);
	write(";");
	printFooter(x);

    }

    public static String getTypeNameForAccessMethods(String typeName){
	typeName = typeName.replace('[','_');
	return typeName.replace('.','_');
    }

    public void printLocalVariableDeclaration(LocalVariableDeclaration x) 
	throws java.io.IOException {
        printHeader(x);
	// Mark statement start ...
	markStart(0,x);
        int m = 0;
        if (x.getModifiers() != null) {
            m = x.getModifiers().size();
            writeKeywordList(x.getModifiers());
        }
        writeElement((m > 0) ? 1 : 0, x.getTypeReference());
	write(" ");
        ImmutableArray<VariableSpecification> varSpecs = x.getVariables();
	boolean wasNoSemicolons = noSemicolons;
	boolean wasNoLinefeed   = noLinefeed;
	noSemicolons = true;
	noLinefeed   = true;
        if (varSpecs != null) {
            writeCommaList(0, 0, 1, varSpecs);
        }
        // !!!!!!!!!! HAS TO BE CHANGED
        //       if (!(x.getStatementContainer() instanceof LoopStatement)) {
        write(";");
        //        }

        // Mark statement end ...
        markEnd(0,x);
        noSemicolons = wasNoSemicolons;
        noLinefeed   = wasNoLinefeed;
        printFooter(x);
    }

    public void printVariableDeclaration(VariableDeclaration x) 
	throws java.io.IOException {

        printHeader(x);
	
	// Mark statement start ...
	markStart(0,x);

        int m = 0;
        if (x.getModifiers() != null) {
            m = x.getModifiers().size();
            writeKeywordList(x.getModifiers());
        }
        writeElement((m > 0) ? 1 : 0, x.getTypeReference());
	write(" ");
        ImmutableArray<? extends VariableSpecification> varSpecs = x.getVariables();
        if (varSpecs != null) {
            writeCommaList(0, 0, 1, varSpecs);
        }
	
	// Mark statement end ...
	markEnd(0,x);

        printFooter(x);
    }

    public void printMethodDeclaration(MethodDeclaration x)
	    throws java.io.IOException {
	printHeader(x);
	Comment[] c = x.getComments();
	int m = c.length;
        for (Comment aC : c) {
            printComment(aC);
        }
	if (x.getModifiers() != null) {
	    ImmutableArray<Modifier> mods = x.getModifiers();
	    m += mods.size();
	    writeKeywordList(mods);
	}
	if (x.getTypeReference() != null) {
	    if (m > 0) {
		writeElement(1, x.getTypeReference());
	    } else {
		writeElement(x.getTypeReference());
	    }
	    writeElement(1, x.getProgramElementName());
	} else if (x.getTypeReference() == null
	        && !(x instanceof ConstructorDeclaration)) {
	    write(" void ");
	    writeElement(1, x.getProgramElementName());
	} else {
	    if (m > 0) {
		writeElement(1, x.getProgramElementName());
	    } else {
		writeElement(x.getProgramElementName());
	    }
	}
	write(" (");
	if (x.getParameters() != null) {
	    writeCommaList(1, x.getParameters());
	}
	write(")");
	if (x.getThrown() != null) {
	    writeElement(1, x.getThrown());
	}
	if (x.getBody() != null) {
	    writeElement(1, x.getBody());
	} else {
	    write(";");
	}
	printFooter(x);
    }

    public void printClassInitializer(ClassInitializer x) 
	throws java.io.IOException {

        printHeader(x);
        int m = 0;
        if (x.getModifiers() != null) {
            m = x.getModifiers().size();
            writeKeywordList(x.getModifiers());
        }
        if (x.getBody() != null) {
            writeElement(m > 0 ? 1 : 0, x.getBody());
        }
        printFooter(x);
    }

    public void printStatementBlock(StatementBlock x) throws java.io.IOException {
        printHeader(x);

	if (!(x.getBody() != null && x.getBody().size() > 0)) {
	    // We have an empty statement block ...
	    
	    // Mark statement start ...
	    markStart(0,x);

	}

	// Hack to insert space after "if (cond)", etc. but not
	// at beginning of diamond.
	if (column!=0) {
	    write(" ");
	}
	write("{");	
	if (x.getBody() != null && x.getBody().size() > 0) {
	    writeLineList(1, +1, 0, x.getBody());
	    writeSymbol(1, -1, "}");
	} else {
	    write("}");

	    // Mark statement end ...
	    markEnd(0,x);

	}
	printFooter(x);
    }

    public void printBreak(Break x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
	
	// Mark statement start ...
	markStart(0,x);

        write("break ");
	noLinefeed=true;
        if (x.getProgramElementName() != null) {
            writeElement(1, x.getProgramElementName());
        }
        write(";");
	noLinefeed=false;

	// Mark statement end ...
	markEnd(0,x);

        printFooter(x);
    }

    public void printContinue(Continue x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);

	// Mark statement start ...
	markStart(0,x);

        write("continue ");
	noLinefeed=true;
        if (x.getProgramElementName() != null) {
            writeElement(1, x.getProgramElementName());
        }
        write(";");
	noLinefeed=false;

	// Mark statement end ...
	markEnd(0,x);

        printFooter(x);
    }

    public void printReturn(Return x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
	
	// Mark statement start ...
	markStart(0,x);

        write("return ");
        if (x.getExpression() != null) {
            noSemicolons = true;
            writeElement(1, x.getExpression());
            noSemicolons = false;            
        }
        write(";");

	// Mark statement end ...
	markEnd(0,x);

        printFooter(x);
    }

    public void printThrow(Throw x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);

	// Mark statement start ...
	markStart(0,x);

        write("throw ");
        if (x.getExpression() != null) {
            noSemicolons = true;
            writeElement(1, x.getExpression());
            noSemicolons = false;
        }
        write(";");

	// Mark statement end ...
	markEnd(0,x);

        printFooter(x);
    }

    public void printDo(Do x) throws java.io.IOException {
       printDo(x, true);
    }

    public void printDo(Do x, boolean includeBody) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);

	// Mark statement start ...
	markStart(0,x);

   write("do");
	if (includeBody) {
      if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
          write(";");
          //w.writeElement(1, body);
      } else {
     if (x.getBody() instanceof StatementBlock) {
                  writeElement(1, 0, x.getBody());
              } else {
                  writeElement(1, +1, 0, x.getBody());
                  changeLevel(-1);
              }
 }        
	}
	else {
	   write(" ... ");
	}
	writeSymbol(1, 0, "while");
	noLinefeed=true;
	noSemicolons=true;
	write(" (");
        if (x.getGuardExpression() != null) {
	    write(" ");
            writeElement(x.getGuardExpression());
	    write(" ");
        }
	noLinefeed=false;
	noSemicolons=false;
        write(");");

	// Mark statement end ...
	markEnd(0,x);
	
        printFooter(x);
    }

    private static void removeChar(StringBuffer sb, char c) {
	for (int i=0; i<sb.length(); i++) {
	    if (sb.charAt(i)==c) {
		sb.deleteCharAt(i);
	    }
	}
    }

    public void printEnhancedFor(EnhancedFor x) throws IOException {
       printEnhancedFor(x, true);
    }

    public void printEnhancedFor(EnhancedFor x, boolean includeBody) throws IOException {
        printHeader(x);
        writeInternalIndentation(x);
        output();

        // Mark statement start ...
        markStart(0, x);

        write("for (");
        noLinefeed = true;
        noSemicolons = true;

        ImmutableArray<LoopInitializer> initializers = x.getInitializers();
        if(initializers != null) {
            LoopInitializer loopInit = initializers.get(0);
            writeElement(1, loopInit);
        }
        
        write(" : ");
        
        if(x.getGuard() != null)
            writeElement(1, x.getGuardExpression());
        
        write(")");
        output();
        noLinefeed = false;
        noSemicolons = false;
        
        if (includeBody) {
           if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
              write(";");
          } else {
              if (x.getBody() instanceof StatementBlock) {
                  writeElement(1, 0, x.getBody());
              } else {
                  writeElement(1, +1, 0, x.getBody());
                  changeLevel(-1);
              }
          }
        }

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printFor(For x) throws java.io.IOException {
       printFor(x, true);
    }

    public void printFor(For x, boolean includeBody) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        output();

        // Mark statement start ...
        markStart(0, x);

        write("for (");
        noLinefeed = true;
        noSemicolons = true;
        write(" ");

        // there is no "getLoopInit" method
        // so get the first child of the for loop
        ILoopInit init = x.getILoopInit();
        if(init != null) {
            if(init instanceof ProgramSV)
                writeElement(init);
            else
                writeCommaList(x.getInitializers());
        } 
        noSemicolons = false;
        write("; ");
        output();
        noSemicolons = true;
        if (x.getGuardExpression() != null) {
            writeElement(1, x.getGuardExpression());
        }
        noSemicolons = false;
        write("; ");
        output();
        noSemicolons = true;
        
        IForUpdates upd = x.getIForUpdates();
        if(upd != null) {
            if(upd instanceof ProgramSV)
                writeElement(1, upd);
            else
                writeCommaList(0, 0, 1, x.getUpdates());
        }
        write(" ");
        write(")");
        output();
        noLinefeed = false;
        noSemicolons = false;
        
        if (includeBody) {
           if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
              write(";");
          } else {
              if (x.getBody() instanceof StatementBlock) {
                  writeElement(1, 0, x.getBody());
              } else {
                  writeElement(1, +1, 0, x.getBody());
                  changeLevel(-1);
              }
          }
        }

        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);
    }

    public void printWhile(While x) throws java.io.IOException {
       printWhile(x, true);
    }

    public void printWhile(While x, boolean includeBody) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
	output();
	noLinefeed=true;
	noSemicolons=true;

	// Mark statement start ...
	markStart(0,x);

	write("while (");
	write(" ");
        if (x.getGuardExpression() != null) {
            writeElement(x.getGuardExpression());
        }
	write(" )"); output();
	noLinefeed=false;
	noSemicolons=false;
	
	if (includeBody) {
        if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
            write(";");
        } else {
	    if (x.getBody() instanceof StatementBlock) {
		writeElement(0, 0, x.getBody());
	    } else {
		writeElement(1, +1, 0, x.getBody());
		changeLevel(-1);
	    }
        }
	}

	// Mark statement end ...
	markEnd(0,x);

        printFooter(x);
    }

    public void printIf(If x) throws java.io.IOException {
       printIf(x, true);
    }

    public void printIf(If x, boolean includeBranches) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
	output();
	
	noLinefeed   = true;
	noSemicolons = true;	

	// Mark statement start ...
	markStart(0,x);

	write("if (");
        if (x.getExpression() != null) {
	    writeElement(1, x.getExpression());
        }
	write(")");

        noLinefeed = false;        
        noSemicolons = false;
        
        if (includeBranches) {
           if (x.getThen() != null) {
              if (x.getThen().getBody() instanceof StatementBlock) {
             writeElement(1, 0, x.getThen());
              } else {
             writeElement(1, +1, 0, x.getThen());
             changeLevel(-1);
              }
               }
               if (x.getElse() != null) {
              writeElement(1, 0, x.getElse());
               }
        }

	// Mark statement end ...
	markEnd(0,x);

        printFooter(x);
    }

    public void printSwitch(Switch x) throws java.io.IOException {
       printSwitch(x, true);
    }

    public void printSwitch(Switch x, boolean includeBranches) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);

	// Mark statement start ...
	markStart(0,x);

        write("switch (");
        if (x.getExpression() != null) {           
            noSemicolons = true;
            writeElement(x.getExpression());
            noSemicolons = false;
        }
        write(")");
        if (includeBranches) {
           write(" {");
           if (x.getBranchList() != null) {
               writeLineList(1, 0, 0, x.getBranchList());
           }
           writeSymbol(1, 0, "}");
        }
	
	// Mark statement end ...
	markEnd(0,x);

        printFooter(x);
    }

    public void printTry(Try x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);

	// // Mark statement start ...
	// markStart(0,x);

        write("try");

        if (x.getBody() != null) {
                writeElement(0, 0, x.getBody());
        }
        if (x.getBranchList() != null) {
	    writeLineList(1, 0, 0, x.getBranchList());
        }

	// // Mark statement end ...
	// markEnd(0,x);

        printFooter(x);
    }

    public void printLabeledStatement(LabeledStatement x) 
	throws java.io.IOException {

        printHeader(x);
	
	
        if (x.getLabel() != null) {
            writeElement(x.getLabel());
            writeToken(":", x);
        } 

        if (x.getBody() != null) {
	    writeElement(1, 0, x.getBody());
        }

        printFooter(x);
    }

    public void printMethodFrame(MethodFrame x) 
	throws java.io.IOException {

        printHeader(x);

	noLinefeed   = false;

	write("method-frame(");
	IProgramVariable pvar = x.getProgramVariable();
	if (pvar != null) {
	    write("result->");
	    writeElement(pvar);
            write(", ");
	} 

	if (x.getExecutionContext() instanceof ExecutionContext) {
	    writeElement(x.getExecutionContext());
	} else {
	    printSchemaVariable((SchemaVariable)x.getExecutionContext());
	} 

	write(")");	
	writeToken(":", x);
	
	noLinefeed = false;
	noSemicolons = false;

        if (x.getBody() != null) {
	    writeElement(0, 0, x.getBody());
        }

        printFooter(x);
    }

    public void printCatchAllStatement(CatchAllStatement x) 
	throws java.io.IOException {
        printHeader(x);
	markStart(0, x);
	write("#catchAll");
	write("(");
	writeElement(x.getParam());
	write(")");
	writeElement(1, x.getBody());        
	markEnd(0, x);
        printFooter(x);	
    }

    public void printMethodBodyStatement(MethodBodyStatement x)
	    throws java.io.IOException {

	boolean wasNoLinefeed = noLinefeed;
	noLinefeed = false;

	printHeader(x);
	writeInternalIndentation(x);
	markStart(0, x);

	IProgramVariable pvar = x.getResultVariable();
	if (pvar != null) {
	    writeElement(pvar);
	    write("=");
	}

	printMethodReference(x.getMethodReference(), false);
	// CHG:
	write("@");
	final TypeReference tr = x.getBodySourceAsTypeReference();
	if (tr instanceof SchemaTypeReference) {
	    printSchemaTypeReference((SchemaTypeReference) tr);
	} else if (tr instanceof SchemaVariable) {
	    printSchemaVariable((SchemaVariable) tr);
	} else {
	    printTypeReference(tr);
	}
	write(";");
	markEnd(0, x);
	printFooter(x);

	noLinefeed = wasNoLinefeed;
    }


    public void printSynchronizedBlock(SynchronizedBlock x) 
	throws java.io.IOException {

        printHeader(x);
        writeInternalIndentation(x);
        write("synchronized");
        if (x.getExpression() != null) {
            write("(");
            writeElement(x.getExpression());
            write(")");
        }
        if (x.getBody() != null) {
            writeElement(1, x.getBody());
        }
        printFooter(x);
    }

    public void printImport(Import x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write("import");
        writeElement(1, x.getReference());
        if (x.isMultiImport()) {
            write(".*;");
        } else {
            write(";");
        }
        printFooter(x);
    }


    public void printExtends(Extends x) throws java.io.IOException {
        printHeader(x);
        if (x.getSupertypes() != null) {
            writeInternalIndentation(x);
            write("extends");
            writeCommaList(0, 0, 1, x.getSupertypes());
        }
        printFooter(x);
    }

    public void printImplements(Implements x) throws java.io.IOException {
        printHeader(x);
        if (x.getSupertypes() != null) {
            writeInternalIndentation(x);
            write("implements");
            writeCommaList(0, 0, 1, x.getSupertypes());
        }
        printFooter(x);
    }

    public void printVariableSpecification(VariableSpecification x)
    throws java.io.IOException {

        printHeader(x);

        // Mark statement start ...
        markStart(0, x);

        x.getProgramVariable().prettyPrint(this);
        //writeElement(x.getProgramElementName());
        for (int i = 0; i < x.getDimensions(); i += 1) {
            write("[]");
        }
        if (x.getInitializer() != null) {
            //            w.writeIndentation(getInternalLinefeeds(),
            // getInternalIndentation());
            write(" = ");
            writeElement(0, 0, 1, x.getInitializer());
        }
        // Mark statement end ...
        markEnd(0, x);

        printFooter(x);

    }

    public void printBinaryAnd(BinaryAnd x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "&");
        printFooter(x);
    }

    public void printBinaryAndAssignment(BinaryAndAssignment x) 
	throws java.io.IOException {

        printHeader(x);
        printOperator(x,  "&=");
        printFooter(x);
    }

    public void printBinaryOrAssignment(BinaryOrAssignment x) 
	throws java.io.IOException {

        printHeader(x);
        printOperator(x,  "|=");
        printFooter(x);
    }

    public void printBinaryXOrAssignment(BinaryXOrAssignment x) 
	throws java.io.IOException {

        printHeader(x);
        printOperator(x,  "^=");
        printFooter(x);
    }

    public void printCopyAssignment(CopyAssignment x) throws java.io.IOException {
        printHeader(x);
	//output();
	//	noLinefeed=true;
        printOperator(x,  "=");
	//	noLinefeed=false;
	//write("\n");
        printFooter(x);	
    }
    
    public void printDivideAssignment(DivideAssignment x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "/=");
        printFooter(x);
    }

    public void printMinusAssignment(MinusAssignment x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "-=");
        printFooter(x);
    }

    public void printModuloAssignment(ModuloAssignment x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "%=");
        printFooter(x);
    }

    public void printPlusAssignment(PlusAssignment x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "+=");
        printFooter(x);
    }

    public void printPostDecrement(PostDecrement x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "--");
        printFooter(x);
    }

    public void printPostIncrement(PostIncrement x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "++");
        printFooter(x);
    }

    public void printPreDecrement(PreDecrement x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "--");
        printFooter(x);
    }

    public void printPreIncrement(PreIncrement x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "++");
        printFooter(x);
    }

    public void printShiftLeftAssignment(ShiftLeftAssignment x) 
	throws java.io.IOException {

        printHeader(x);
        printOperator(x,  "<<=");
        printFooter(x);
    }

    public void printShiftRightAssignment(ShiftRightAssignment x) 
	throws java.io.IOException {

        printHeader(x);
        printOperator(x,  ">>=");
        printFooter(x);
    }

    public void printTimesAssignment(TimesAssignment x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "*=");
        printFooter(x);
    }

    public void printUnsignedShiftRightAssignment(UnsignedShiftRightAssignment x) 
	throws java.io.IOException {

        printHeader(x);
        printOperator(x,  ">>>=");
        printFooter(x);
    }

    public void printBinaryNot(BinaryNot x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "~");
        printFooter(x);
    }

    public void printBinaryOr(BinaryOr x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "|");
        printFooter(x);
    }

    public void printBinaryXOr(BinaryXOr x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "^");
        printFooter(x);
    }
    
    public void printConditional(Conditional x) throws java.io.IOException {
        printHeader(x);

        boolean addParentheses = x.isToBeParenthesized();
        if (x.getArguments() != null) {
            if (addParentheses) {
                write("(");
            }
            writeElement(0, x.getArguments().get(0));
            write(" ?");
            writeElement(1, x.getArguments().get(1));
            write(" :");
            writeElement(1, x.getArguments().get(2));
            if (addParentheses) {
                write(")");
            }
        }
        printFooter(x);
    }

    public void printDivide(Divide x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "/");
        printFooter(x);
    }

    public void printEquals(Equals x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "==");
        printFooter(x);
    }

    public void printGreaterOrEquals(GreaterOrEquals x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  ">=");
        printFooter(x);
    }

    public void printGreaterThan(GreaterThan x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  ">");
        printFooter(x);
    }

    public void printLessOrEquals(LessOrEquals x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "<=");
        printFooter(x);
    }

    public void printLessThan(LessThan x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "<");
        printFooter(x);
    }

    public void printNotEquals(NotEquals x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "!=");
        printFooter(x);
    }

    public void printNewArray(NewArray x) throws java.io.IOException {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            write("(");
        }
        writeInternalIndentation(x);
        write("new ");
                
        writeElement(1, x.getTypeReference());
        int i = 0;
        if (x.getArguments() != null) {
            for (; i < x.getArguments().size(); i += 1) {
                write("[");
                writeElement(x.getArguments().get(i));
                write("]");
            }
        }
        for (; i < x.getDimensions(); i += 1) {
            write("[]");
        }
        if (x.getArrayInitializer() != null) {
            writeElement(1, x.getArrayInitializer());
        }
        if (addParentheses) {
            write(")");
        }
        printFooter(x);
    }

    public void printInstanceof(Instanceof x) throws java.io.IOException {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            write("(");
        }
        if (x.getArguments() != null) {
            writeElement(0, x.getExpressionAt(0));
        }
        writeInternalIndentation(x);
        write(" instanceof ");
        if (x.getTypeReference() != null) {
            writeElement(1, x.getTypeReference());
        }
        if (addParentheses) {
            write(")");
        }
        printFooter(x);
    }


    public void printExactInstanceof(ExactInstanceof x) throws java.io.IOException {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            write("(");
        }
        if (x.getArguments() != null) {
            writeElement(0, x.getExpressionAt(0));
        }
        writeInternalIndentation(x);
        write(" exactInstanceof ");
        if (x.getTypeReference() != null) {
            writeElement(1, x.getTypeReference());
        }
        if (addParentheses) {
            write(")");
        }
        printFooter(x);
    }



    public void printNew(New x) throws java.io.IOException {
        printHeader(x);

	// Mark statement start ...
	markStart(0,x);

        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            write("(");
        }
        if (x.getReferencePrefix() != null) {
            writeElement(0, x.getReferencePrefix());
            write(".");
        }
        writeInternalIndentation(x);
        write("new ");
        
        writeElement(1, x.getTypeReference());
	write(" (");
        if (x.getArguments() != null) {
            writeCommaList(x.getArguments());
        }
        write(")");
        if (x.getClassDeclaration() != null) {
            writeElement(1, x.getClassDeclaration());
        }
        if (addParentheses) {
            write(")");
        }
	// !!!!!!!!!! HAS TO BE CHANGED
//	if (x.getStatementContainer() != null && fileWriterMode) {
//	   write(";");
//	}

	// Mark statement end ...
	markEnd(0,x);
        printFooter(x);
    }

    public void printTypeCast(TypeCast x) throws java.io.IOException {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            write("(");
        }
        writeInternalIndentation(x);
        write("(");
        if (x.getTypeReference() != null) {
            writeElement(0, x.getTypeReference());
        }
        write(")");
        if (x.getArguments() != null) {
            writeElement(0, x.getArguments().get(0));
        }
        if (addParentheses) {
            write(")");
        }
        printFooter(x);
    }

    public void printLogicalAnd(LogicalAnd x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "&&");
        printFooter(x);
    }

    public void printLogicalNot(LogicalNot x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "!");
        printFooter(x);
    }

    public void printLogicalOr(LogicalOr x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "||");
        printFooter(x);
    }

    public void printMinus(Minus x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "-");
        printFooter(x);
    }

    public void printModulo(Modulo x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "%");
        printFooter(x);
    }

    public void printNegative(Negative x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "-");
        printFooter(x);
    }

    public void printPlus(Plus x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "+");
        printFooter(x);
    }

    public void printPositive(Positive x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "+");
        printFooter(x);
    }

    public void printShiftLeft(ShiftLeft x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "<<");
        printFooter(x);
    }

    public void printShiftRight(ShiftRight x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  ">>");
        printFooter(x);
    }

    public void printTimes(Times x) throws java.io.IOException {
        printHeader(x);
        printOperator(x,  "*");
        printFooter(x);
    }

    public void printUnsignedShiftRight(UnsignedShiftRight x) 
	throws java.io.IOException {

        printHeader(x);
        printOperator(x,  ">>>");
        printFooter(x);
    }

    public void printArrayReference(ArrayReference x) throws java.io.IOException {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
        }
        if (x.getDimensionExpressions() != null) {
            int s = x.getDimensionExpressions().size();
            for (int i = 0; i < s; i += 1) {
                write("[");
                writeElement(x.getDimensionExpressions().get(i));
                write("]");
            }
        }
        printFooter(x);
    }

    public void printMetaClassReference(MetaClassReference x) 
	throws java.io.IOException {

        printHeader(x);
        if (x.getTypeReference() != null) {
            writeElement(x.getTypeReference());
            writeToken(".", x);
        }
        write("class");
        printFooter(x);
    }

    public void printMethodReference(MethodReference x) 
	throws java.io.IOException {       
        printMethodReference(x, !noSemicolons);
    }


    protected void printMethodReference(MethodReference x,
            boolean withSemicolon) 
	throws java.io.IOException {      
	printHeader(x);       
	// Mark statement start ...
	markStart(0,x);

        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            write(".");
        }
        if (x.getProgramElementName() != null) {
        	x.getMethodName().prettyPrint(this);
            //writeElement(x.getProgramElementName());
        }
 
	write("(");
	boolean wasNoSemicolons = noSemicolons;
	boolean wasNoLinefeed   = noLinefeed;
	noLinefeed   = true;
	noSemicolons = true;      
        if (x.getArguments() != null) {
            writeCommaList(x.getArguments());
        }	
	write(")");
	if (withSemicolon) {
            write(";");           
        }
	noLinefeed   = wasNoLinefeed;
	noSemicolons = wasNoSemicolons;       
	output();

	// Mark statement end ...
	markEnd(0,x);
	
    }

    public void printMethod(IProgramMethod x) throws java.io.IOException {
	//        printHeader(x);
	write(x.name().toString());
	//        printFooter(x);
    }

    public void printFullMethodSignature(IProgramMethod x) throws java.io.IOException {
       printHeader(x);
       writeFullMethodSignature(x);
       printFooter(x);
    }
    
    protected void writeFullMethodSignature(IProgramMethod x) throws java.io.IOException {
        write(x.getName());
        write("(");
        boolean afterFirst = false;
        for (ParameterDeclaration pd : x.getParameters()) {
            if (afterFirst) {
                write(", ");
            }
            else {
                afterFirst = true;
            }
            boolean originalNoLinefeed = noLinefeed;
            try {
               noLinefeed = true;
               printTypeReference(pd.getTypeReference(), true);
            }
            finally {
               noLinefeed = originalNoLinefeed;
            }
        }
        write(")");
    }

    public void printExecutionContext(ExecutionContext x) 
	throws java.io.IOException {
	write("source=");
	writeFullMethodSignature(x.getMethodContext());
	write("@");
	writeElement(x.getTypeReference());
	if (x.getRuntimeInstance() != null) {
	    write(",this=");
	    writeElement(x.getRuntimeInstance());
	}
    }

    public void printSuperConstructorReference(SuperConstructorReference x) 
	throws java.io.IOException {

        printHeader(x);
	markStart(0,x);

        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            write(".");
        }
	writeToken("super (", x);
        if (x.getArguments() != null) {
            writeCommaList(0, 0, 0, x.getArguments());
        }
        write(");");
	markEnd(0,x);
        printFooter(x);
    }

    public void printThisConstructorReference(ThisConstructorReference x) 
	throws java.io.IOException {

        printHeader(x);
	markStart(0,x);
        writeInternalIndentation(x);
	write("this (");
        if (x.getArguments() != null) {
            writeCommaList(x.getArguments());
        }
        write(");");
	markEnd(0,x);
        printFooter(x);
    }

    public void printSuperReference(SuperReference x) throws java.io.IOException {
        printHeader(x);
	markStart(0,x);
        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            writeToken(".super", x);
        } else {
            writeToken("super", x);
        }
	markEnd(0,x);
        printFooter(x);
    }

    public void printThisReference(ThisReference x) throws java.io.IOException {
        printHeader(x);
	markStart(0,x);
        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            writeToken(".this", x);
        } else {
            writeToken("this", x);
        }
	markEnd(0,x);
        printFooter(x);
    }
    
    public void printArrayLengthReference(ArrayLengthReference x) 
	throws java.io.IOException {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            writeElement(x.getReferencePrefix());
            write(".");
        }
        writeToken("length", x);
        printFooter(x);
    }

    public void printThen(Then x) throws java.io.IOException {
        printHeader(x);
        if (x.getBody() != null) {
            writeElement(x.getBody());
        }
        printFooter(x);
    }

    public void printElse(Else x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write("else ");
        if (x.getBody() != null) {
	    if (x.getBody() instanceof StatementBlock) {
		writeElement(1, 0, x.getBody());
	    } else {
		writeElement(1, +1, 0, x.getBody());
		changeLevel(-1);
	    }
	}
        
        printFooter(x);
    }

    public void printCase(Case x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write("case ");
        if (x.getExpression() != null) {
            boolean wasNoSemicolons = noSemicolons;
            noSemicolons = true;
            writeElement(1, x.getExpression());
            noSemicolons = wasNoSemicolons;
        }
        write(":");
        if (x.getBody() != null && x.getBody().size() > 0) {
            writeLineList(1, +1, 0, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void printCatch(Catch x) throws java.io.IOException {
        printHeader(x);
	writeToken("catch (", x);
        if (x.getParameterDeclaration() != null) {
	    noLinefeed=true;           
            noSemicolons = true;
            writeElement(x.getParameterDeclaration());
        }
        write(")");
        noSemicolons = false;
	noLinefeed=false;
        if (x.getBody() != null) {
            writeElement(1, x.getBody());
        }
        printFooter(x);
    }

    public void printDefault(Default x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write("default:");
        if (x.getBody() != null && x.getBody().size() > 0) {
            writeLineList(1, +1, 0, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void printFinally(Finally x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
	noLinefeed = true;
	output();
	noLinefeed = false;
        write("finally");
        if (x.getBody() != null) {
            writeElement(1, x.getBody());
        }
        printFooter(x);
    }

    public void printModifier(Modifier x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
        write(x.getText());
        printFooter(x);
    }

    public void printSchemaVariable(SchemaVariable x) throws java.io.IOException {
    	if(x instanceof ProgramSV){
    		if (!noSemicolons) {
    			markStart(0,x);
    		}
    		Object o = instantiations.getInstantiation(x); 
    		if (o == null) {
    		    printHeader((ProgramSV)x);
    		    writeInternalIndentation((ProgramSV)x);
    		    write(x.name().toString());
    		    printFooter((ProgramSV)x);
    		} else {
    		    //logger.debug(o.toString() + "  " + o.getClass().getName());
    			//Debug.assertTrue(o instanceof ProgramElement);
    			if (o instanceof ProgramElement) {
    				((ProgramElement)o).prettyPrint(this);
    			} else if (o instanceof ImmutableArray/*<ProgramElement>*/) {
    				writeBlockList((ImmutableArray<ProgramElement>)o);
    			} else {
    				Debug.log4jWarn("No PrettyPrinting available for " + o.getClass().getName(),
    						PrettyPrinter.class.getName());
    			}
    		}
    		if (!noSemicolons) {
    			markEnd(0,x);
    		}
    	}else{
    	    Debug.fail("That cannot happen! Don't know how to pretty print non program SV in programs.");
    	}
    	
    }
   

    public void printEmptyStatement(EmptyStatement x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
	
	// Mark statement start ...
	markStart(0,x);
       	
        write(";");
        
	// Mark statement end ...
	markEnd(0,x);
       	
	printFooter(x);
    }

    public void printComment(Comment x) throws java.io.IOException {
	write("/*" + x.getText() + "*/");
    }

    public void printParenthesizedExpression(ParenthesizedExpression x) 
	throws IOException {

        writeToken("(", x);
        if (x.getArguments() != null) {
            writeElement(x.getArguments().get(0));
        }
        write(")");
	output();
    }    



    public void printPassiveExpression(PassiveExpression x) 
	throws IOException {

        writeToken("@(", x);
        if (x.getArguments() != null) {
            writeElement(x.getArguments().get(0));
        }
        write(")");
	output();
    }

    public void printTransactionStatement(TransactionStatement x) throws java.io.IOException {
        printHeader(x);
        writeInternalIndentation(x);
    
    // Mark statement start ...
    markStart(0,x);

        write(x.toString());
        write(";");

        // Mark statement end ...
    markEnd(0,x);

        printFooter(x);
    }

    
}