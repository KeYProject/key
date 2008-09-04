//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//Universitaet Koblenz-Landau, Germany
//Chalmers University of Technology, Sweden

//The KeY system is private by the GNU General private License. 
//See LICENSE.TXT for details.



package de.uka.ilkd.key.java;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Type;
import recoder.java.NonTerminalProgramElement;
import recoder.list.generic.ASTList;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Ghost;
import de.uka.ilkd.key.java.declaration.modifier.Model;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.recoderext.ImplicitIdentifier;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * Objects of this class can be used to transform an AST returned by the recoder
 * library to the corresponding yet immutable KeY data structures.
 * 
 * Call the method process() to convert an arbitrary object.
 * 
 * The method callConvert is used to perform a run-time dispatch upon the
 * parameters.
 * 
 * The actual conversion is done in convert-methods which must be declared
 * public due to the used reflection method lookup function.
 * 
 * There is a general method {@link #callConvert(recoder.java.ProgramElement)}
 * that does the job in general. Several special cases must be treated
 * separately.
 * 
 * This code used to be part of {@link Recoder2KeY} and has been 'out-sourced'.
 * 
 * @author mattias ulbrich
 * @since Jul-07
 */
public class Recoder2KeYConverter {

    // -------- public part

    public ProgramElement process(recoder.java.ProgramElement pe) {
        Object result = callConvert(pe);
        assert result instanceof ProgramElement : "result must be a ProgramElement";
        return (ProgramElement) result;
    }

    public ProgramMethod processDefaultConstructor(
            recoder.abstraction.DefaultConstructor df) {
        return convert(df);
    }

    public CompilationUnit processCompilationUnit(
            recoder.java.CompilationUnit cu, String context) {
        currentClass = context;
        Object result = process(cu);
        currentClass = null;

        assert result instanceof CompilationUnit : "a compilation unit must result in a compilation unit!";

        return (CompilationUnit) result;
    }

    public Recoder2KeYConverter(Recoder2KeY rec2key) {
        super();
        this.rec2key = rec2key;
    }

    // -------- implementation part

    /**
     * caches access to methods for reflection. It is a HashMap<Class, Method>
     */
    private final HashMap methodCache = new HashMap(400);

    /**
     * caches constructor access for reflection. It is a HashMap<Class,
     * Constructor>
     */
    private final HashMap constructorCache = new HashMap(400);

    /**
     * Hashmap from <code>recoder.java.declaration.FieldSpecification</code>
     * to <code>ProgramVariable</code>; this is necessary to avoid cycles
     * when converting initializers. Access to this map is performed via the
     * method <code>getProgramVariableForFieldSpecification</code>
     */
    private HashMap fieldSpecificationMapping = new HashMap();

    /**
     * methodsDeclaring contains the recoder method declarations as keys that
     * have been started to convert but are not yet finished. The mapped value
     * is the reference to the later completed ProgramMethod.
     */
    private HashMap methodsDeclaring = new HashMap();

    /**
     * locClass2finalVar stores the final variables that need to be passed
     * to the constructor of an anonymous class. 
     */
    protected HashMap locClass2finalVar = null;
    
    /**
     * stores the class that is currently processed
     */
    private String currentClass;

    /**
     * flag which is true if currently in a for initialiser or update
     */
    private boolean inLoopInit = false;

    /**
     * the associated Recoder2KeY object
     */
    private Recoder2KeY rec2key;

    /**
     * retrieve a key type using the converter available from Recoder2KeY
     * 
     * @param javaType
     *            type to look up
     * @return the result from the type converter
     */
    private KeYJavaType getKeYJavaType(Type javaType) {
        return getTypeConverter().getKeYJavaType(javaType);
    }

    /**
     * retrieve the type converter from the associated Recoder2KeY
     * 
     * @return the type converter, not null.
     */
    private Recoder2KeYTypeConverter getTypeConverter() {
        return rec2key.getTypeConverter();
    }

    /**
     * retrieve the service configuration from the associated Recoder2KeY.
     * 
     * @return the service configuration, not null.
     */
    private CrossReferenceServiceConfiguration getServiceConfiguration() {
        return rec2key.getServiceConfiguration();
    }

    /**
     * retrieve the recoder<->key mapping from the associated Recoder2KeY.
     * 
     * @return the mapping, not null.
     */
    protected KeYRecoderMapping getMapping() {
        // quite contra-intuitive naming, yet right here
        return rec2key.rec2key();
    }

    /**
     * are we currently parsing library code? Ask the associated Recoder2KeY
     * 
     * @see Recoder2KeY#isParsingLibs()
     * @return true if libs are parsed at the moment
     */
    private boolean isParsingLibs() {
        return rec2key.isParsingLibs();
    }

    /**
     * convert a recoder ProgramElement to a corresponding KeY data structure
     * entity.
     * 
     * Almost always the returned type carries the same Classname but in a KeY
     * rather than a recoder package.
     * 
     * Determines the right convert method using reflection
     * 
     * @param pe
     *            the recoder.java.JavaProgramElement to be converted, not null.
     * 
     * @return the converted element
     * 
     * @throws ConvertException
     *             if the conversion fails
     */
    protected Object callConvert(recoder.java.ProgramElement pe)
    throws ConvertException {

        if (pe == null)
            throw new ConvertException("cannot convert 'null'");

        Class contextClass = pe.getClass();
        Method m = (Method) methodCache.get(contextClass);

        // if not in cache, search it - and fill the cache
        if (m == null) {
            Class[] context = new Class[] { contextClass };

            // remember all superclasses for the cache
            LinkedList l = new LinkedList();

            while (m == null && context[0] != null) {
                l.add(contextClass);

                try {
                    m = getClass().getMethod("convert", context);
                } catch (NoSuchMethodException nsme) {
                    Debug.out("convert method not found for: " + context[0]);
                    context[0] = contextClass = context[0].getSuperclass();
                }
            }

            if (m == null)
                throw new ConvertException(
                        "Could not find convert method for class "
                        + pe.getClass());

            Iterator it = l.iterator();
            while (it.hasNext()) {
                methodCache.put(it.next(), m);
            }
        }

        // method found - now make the call to it.

        Object result = null;
        try {
            result = m.invoke(this, new Object[] { pe });
        } catch (IllegalAccessException iae) {
            Debug.out("recoder2key: cannot access method ", iae);
            throw new ConvertException("recoder2key: cannot access method", iae);
        } catch (IllegalArgumentException iarg) {
            Debug.out("recoder2key: wrong method arguments ", iarg);			
            throw new ConvertException("recoder2key: wrong method arguments",
                    iarg);
        } catch (InvocationTargetException ite) {
            Debug.out("recoder2key: called method " + m + " threw exception ", ite
                    .getTargetException());
            if (ite.getTargetException() instanceof ConvertException) {
                throw (ConvertException) ite.getTargetException();
            } else {
                Recoder2KeY.reportError("called method " + m
                        + " threw exception.", ite.getTargetException());
            }
        }

        // set the parental class attribute if available
        if ((currentClass != null) && (result instanceof Statement)
                && !(result instanceof SchemaVariable)) {
            ((JavaProgramElement) result).setParentClass(currentClass);
        }

        Debug.assertTrue(result instanceof ProgramElement || result == null,
                "the result is not a ProgramElement but", result);

        return result;

    }

    // ==== HELPER FUNCTIONS ===============================================

    /**
     * iterate over all children and call convert upon them. Gather the
     * resulting KeY structures in an ExtList.
     * 
     * In addition to the child ast-branches, all comments are gathered also.
     * 
     * @param pe
     *            the NonTerminalProgramElement that needs its children before
     *            being converted
     * @return the list of children after conversion
     */
    protected ExtList collectChildren(recoder.java.NonTerminalProgramElement pe) {
        ExtList children = new ExtList();
        for (int i = 0, childCount = pe.getChildCount(); i < childCount; i++) {
            children.add(callConvert(pe.getChildAt(i)));
        }

        // convert all comments for pe
        ASTList<recoder.java.Comment> l = pe.getComments();
        if (l != null) {
            for (int i = 0, sz = l.size(); i < sz; i++) {
                children.add(convert(l.get(i)));
            }
        }

        children.add(positionInfo(pe));
        return children;
    }
    
    /**
     * replace some numbers from anonymous class names.
     * needed by the translation of anonymous classes. 
     */
    static String makeAdmissibleName(String s){
        return s;
        /*
         int i = s.indexOf(".");
         while(i!=-1){
             if(s.charAt(i+1)<='9' && s.charAt(i+1)>='0') {
                 s = s.substring(0, i)+"_"+s.substring(i+1);
             }
             i = s.indexOf(".", i+1);
         }
         return s;
        */
    }


    /**
     * collects comments and adds their converted KeY-counterpart to the list of
     * children
     * 
     * @param pe
     *            the ProgramElement that needs its comments before being
     *            converted
     * @return the list of comments after conversion
     */
    private ExtList collectComments(recoder.java.ProgramElement pe) {
        ExtList children = new ExtList();
        ASTList<recoder.java.Comment> l = pe.getComments();
        if (l != null) {
            for (int i = 0, sz = l.size(); i < sz; i++) {
                children.add(convert(l.get(i)));
            }
        }
        return children;
    }

    /**
     * collects both comments and children of a program element
     * 
     * @param pe
     *            program element
     * @return freshly created list of children after conversion and converted
     *         comments
     */
    private ExtList collectChildrenAndComments(recoder.java.ProgramElement pe) {
        ExtList ret = new ExtList();

        if (pe instanceof recoder.java.NonTerminalProgramElement)
            ret.addAll(collectChildren((NonTerminalProgramElement) pe));
        ret.addAll(collectComments(pe));

        return ret;
    }

    /**
     * convert recoder position info to key position info
     * 
     * @param se
     *            the sourcelement to extract from, not null
     * @return the newly created PositionInfo
     */
    private PositionInfo positionInfo(recoder.java.SourceElement se) {
        Position relPos = new Position(se.getRelativePosition().getLine(), se
                .getRelativePosition().getColumn());
        Position startPos = new Position(se.getStartPosition().getLine(), se
                .getStartPosition().getColumn());
        Position endPos = new Position(se.getEndPosition().getLine(), se
                .getEndPosition().getColumn());
        if ((!inLoopInit))
            return new PositionInfo(relPos, startPos, endPos, currentClass);
        else
            return new PositionInfo(relPos, startPos, endPos);

    }

    /**
     * @return a literal constant representing the value of <code>p_er</code>
     */
    private Literal getLiteralFor(
            recoder.service.ConstantEvaluator.EvaluationResult p_er) {
        switch (p_er.getTypeCode()) {
        case recoder.service.ConstantEvaluator.BOOLEAN_TYPE:
            return BooleanLiteral.getBooleanLiteral(p_er.getBoolean());
        case recoder.service.ConstantEvaluator.CHAR_TYPE:
            return new CharLiteral(p_er.getChar());
        case recoder.service.ConstantEvaluator.DOUBLE_TYPE:
            return new DoubleLiteral(p_er.getDouble());
        case recoder.service.ConstantEvaluator.FLOAT_TYPE:
            return new FloatLiteral(p_er.getFloat());
        case recoder.service.ConstantEvaluator.BYTE_TYPE:
            return new IntLiteral(p_er.getByte());
        case recoder.service.ConstantEvaluator.SHORT_TYPE:
            return new IntLiteral(p_er.getShort());
        case recoder.service.ConstantEvaluator.INT_TYPE:
            return new IntLiteral(p_er.getInt());
        case recoder.service.ConstantEvaluator.LONG_TYPE:
            return new LongLiteral(p_er.getLong());
        case recoder.service.ConstantEvaluator.STRING_TYPE:
            if (p_er.getString() == null)
                return NullLiteral.NULL;
            return new StringLiteral(p_er.getString());
        default:
            throw new ConvertException("Don't know how to handle type "
                    + p_er.getTypeCode() + " of " + p_er);
        }
    }

    /**
     * extracts all field specifications out of the given list. Therefore it
     * descends into field declarations.
     * 
     * @param list
     *            the ExtList with the members of a type declaration
     * @return a ListOfField the includes all field specifications found int the
     *         field declaration of the given list
     */
    private ListOfField filterField(ExtList list) {
        ListOfField result = SLListOfField.EMPTY_LIST;
        Iterator it = list.iterator();
        while (it.hasNext()) {
            Object pe = it.next();
            if (pe instanceof FieldDeclaration) {
                result = result.prepend(filterField((FieldDeclaration) pe));
            }
        }
        return result;
    }

    /**
     * extracts all fields out of fielddeclaration
     * 
     * @param field
     *            the FieldDeclaration of which the field specifications have to
     *            be extracted
     * @return a ListOfField the includes all field specifications found int the
     *         field declaration of the given list
     */
    private ListOfField filterField(FieldDeclaration field) {
        ListOfField result = SLListOfField.EMPTY_LIST;
        ArrayOfFieldSpecification spec = field.getFieldSpecifications();
        for (int i = spec.size() - 1; i >= 0; i--) {
            result = result.prepend(spec.getFieldSpecification(i));
        }
        return result;
    }

    /**
     * retrieves a field with the given name out of the list
     * 
     * @param name
     *            a String with the name of the field to be looked for
     * @param fields
     *            the ListOfField where we have to look for the field
     * @return the program variable of the given name or null if not found
     */
    private ProgramVariable find(String name, ListOfField fields) {
        IteratorOfField it = fields.iterator();
        while (it.hasNext()) {
            Field field = it.next();
            if (name.equals(field.getName())) {
                return (ProgramVariable) ((FieldSpecification) field)
                .getProgramVariable();
            }
        }
        return null;
    }

    // ==== CONVERT METHODS ================================================

    // ----- the standard mechanism

    /**
     * The default procedure.
     * 
     * It iterates over all children, calls convert upon them
     * 
     * collect all children, convert them. Create a new instance of the
     * corresponding KeY class and call its constructor with the list of
     * children.
     * 
     * @param pe
     *            the recoder.java.ProgramElement to be converted
     * @return the converted de.uka.ilkd.key.java.JavaProgramElement, null if
     *         there has been an exception
     */
    public ProgramElement convert(recoder.java.JavaProgramElement pe) {
        ProgramElement result = null;
        ExtList parameter;

        if (pe instanceof recoder.java.JavaNonTerminalProgramElement) {
            parameter = collectChildren((recoder.java.JavaNonTerminalProgramElement) pe);
        } else {
            parameter = new ExtList();
        }

        // store also all comments for this element:
        parameter.addAll(collectComments(pe));

        try {
            result = (ProgramElement) getKeYClassConstructor(pe.getClass())
            .newInstance(new Object[] { parameter });
            return result;
        } catch (Exception e) {
            Debug.out("recoder2key: invocation of constructor failed.", e);
            Recoder2KeY.reportError("Invocation of the constructor failed", e);
            throw new Error("unreachable"); // this line is not reachable
            // because reportError fails under
            // any circumstances
        }
    }

    /**
     * gets the KeY-Class related to the recoder one
     * 
     * @param recoderClass
     *            the original Class within recoder
     * @return the related KeY Class
     * @throws ConvertException
     *             for various reasons
     */
    private Class getKeYClass(Class recoderClass) {
        String className = getKeYName(recoderClass);
        try {
            return Class.forName(className);
        } catch (ClassNotFoundException cnfe) {
            Debug.out("There is an AST class " +className + " missing at KeY.", cnfe);
            throw new ConvertException("There is an AST class missing at KeY.",
                    cnfe);
        } catch (ExceptionInInitializerError initErr) {
            Debug.out("recoder2key: Failed initializing class.", initErr);
            throw new ConvertException("Failed initializing class.", initErr);
        } catch (LinkageError le) {
            Debug.out("recoder2key: Linking class failed.", le);
            throw new ConvertException("Linking class failes", le);
        }
    }

    private static int RECODER_PREFIX_LENGTH = "recoder.".length();

    /**
     * constructs the name of the corresponding KeYClass
     * 
     * @param recoderClass
     *            Class that is the original recoder
     * @return String containing the KeY-Classname
     */
    private String getKeYName(Class recoderClass) {
        return "de.uka.ilkd.key."
        + recoderClass.getName().substring(RECODER_PREFIX_LENGTH);
    }

    /**
     * determines the right standard constructor of the KeYClass.
     * 
     * Use a cache to only look up classes once.
     * 
     * @param recoderClass
     *            the Class of the recoder AST object
     * @return the Constructor of the right KeY-Class
     */
    private Constructor getKeYClassConstructor(Class recoderClass) {
        Constructor result = null;
        try {
            result = (Constructor) constructorCache.get(recoderClass);

            if (result == null) {
                result = getKeYClass(recoderClass).getConstructor(
                        new Class[] { ExtList.class });
                constructorCache.put(recoderClass, result);
            }
        } catch (NoSuchMethodException nsme) {
            Debug.out("recoder2key: constructor not found. ", nsme);
        } catch (SecurityException se) {
            Debug.out("recoder2key: access denied. ", se);
        }
        return result;
    }

    /**
     * store an element to the recoder<->key mapping.
     * 
     * @param r
     *            the recoder element (not null)
     * @param k
     *            the key element (not null)
     */
    protected void insertToMap(recoder.ModelElement r, ModelElement k) {

        if (r != null) {
            getMapping().put(r, k);
        } else {
            Debug.out("Tried to store element for null-key - ignored");
        }
    }

    // ------------------- operators ----------------------

     public Instanceof convert(recoder.java.expression.operator.Instanceof rio) {
         return new Instanceof((Expression) callConvert(rio.getExpressionAt(0)),
                 (TypeReference) callConvert(rio.getTypeReference()));
     }

    /**
     * converts the recoder.java.expression.operator.NewArray node to the
     * KeYDependance
     */
    public NewArray convert(recoder.java.expression.operator.NewArray newArr) {
        // first we need to collect all children
        ExtList children = collectChildren(newArr);
        // now we have to extract the array initializer
        // is stored separately and must not appear in the children list
        ArrayInitializer arrInit = (ArrayInitializer) children
        .get(ArrayInitializer.class);
        children.remove(arrInit);

        recoder.abstraction.Type javaType = getServiceConfiguration()
        .getCrossReferenceSourceInfo().getType(newArr);

        return new NewArray(children, getKeYJavaType(javaType), arrInit, newArr
                .getDimensions());
    }

    // ------------------- literals --------------------------------------

    /**
     * converts the recoder.java.Comment to the KeYDependance
     */
    public Comment convert(recoder.java.Comment rc) {
        return new Comment(rc.getText(), positionInfo(rc));
    }

    /** convert a recoder IntLiteral to a KeY IntLiteral */
    public IntLiteral convert(recoder.java.expression.literal.IntLiteral intLit) {
        return new IntLiteral(collectComments(intLit), intLit.getValue());
    }

    /** convert a recoder BooleanLiteral to a KeY BooleanLiteral */
    public BooleanLiteral convert(
            recoder.java.expression.literal.BooleanLiteral booleanLit) {

        // if there are comments to take into consideration
        // change parameter to ExtList
        // TODO make comments available

        return (booleanLit.getValue() ? BooleanLiteral.TRUE
                : BooleanLiteral.FALSE);
    }

    /** convert a recoder StringLiteral to a KeY StringLiteral */
    public StringLiteral convert(
            recoder.java.expression.literal.StringLiteral stringLit) {
        return new StringLiteral(collectComments(stringLit), stringLit
                .getValue());
    }

    /** convert a recoder DoubleLiteral to a KeY DoubleLiteral */
    public DoubleLiteral convert(
            recoder.java.expression.literal.DoubleLiteral doubleLit) {
        return new DoubleLiteral(collectComments(doubleLit), doubleLit
                .getValue());
    }

    /** convert a recoder FloatLiteral to a KeY FloatLiteral */
    public FloatLiteral convert(
            recoder.java.expression.literal.FloatLiteral floatLit) {

        return new FloatLiteral(collectComments(floatLit), floatLit.getValue());
    }

    /** convert a recoder LongLiteral to a KeY LongLiteral */
    public LongLiteral convert(
            recoder.java.expression.literal.LongLiteral longLit) {

        return new LongLiteral(collectComments(longLit), longLit.getValue());
    }

    /** convert a recoder CharLiteral to a KeY CharLiteral */
    public CharLiteral convert(
            recoder.java.expression.literal.CharLiteral charLit) {

        return new CharLiteral(collectComments(charLit), charLit.getValue());
    }

    /** convert a recoder NullLiteral to a KeY NullLiteral */
    public NullLiteral convert(
            recoder.java.expression.literal.NullLiteral nullLit) {

        recoder.abstraction.Type javaType = getServiceConfiguration()
        .getCrossReferenceSourceInfo().getType(nullLit);
        getKeYJavaType(javaType);

        // if there are comments to take into consideration
        // change parameter to ExtList
        // TODO make comments available
        return NullLiteral.NULL;
    }

    // ----------------------------------------------------------

    /** convert a recoder Identifier to a KeY Identifier */
    public ProgramElementName convert(recoder.java.Identifier id) {
        return VariableNamer.parseName(id.getText(),
                (Comment[]) collectComments(id).collect(Comment.class));
    }

    public ProgramElementName convert(ImplicitIdentifier id) {

        return new ProgramElementName(id.getText(),
                (Comment[]) collectComments(id).collect(Comment.class));
    }

    /** convert a recoderext MethodFrameStatement to a KeY MethodFrameStatement */
    public MethodFrame convert(
            de.uka.ilkd.key.java.recoderext.MethodCallStatement rmcs) {
        ProgramVariable resVar = null;
        if (rmcs.getResultVariable() != null) {
            recoder.java.Expression rvar = rmcs.getResultVariable();
            if (rvar instanceof recoder.java.reference.VariableReference) {
                resVar = convert((recoder.java.reference.VariableReference) rvar);
            } else if (rvar instanceof recoder.java.reference.UncollatedReferenceQualifier) {
                try {
                    resVar = (ProgramVariable) callConvert(rvar);
                } catch (ClassCastException e) {
                    throw new ConvertException(
                    "recoder2key: Expression is not a variable reference.");
                }
            }
        }
        StatementBlock block = null;
        if (rmcs.getBody() != null) {
            block = (StatementBlock) callConvert(rmcs.getBody());
        }

        return new MethodFrame(resVar, (ExecutionContext) convert(rmcs
                .getExecutionContext()), block);
    }

    /** convert a recoderext MethodBodyStatement to a KeY MethodBodyStatement */
    public MethodBodyStatement convert(
            de.uka.ilkd.key.java.recoderext.MethodBodyStatement rmbs) {

        final TypeReference bodySource = convert(rmbs.getBodySource());
        final IProgramVariable resultVar = rmbs.getResultVariable() != null ? (IProgramVariable) callConvert(rmbs
                .getResultVariable())
                : null;
        final ReferencePrefix invocationTarget = (ReferencePrefix) callConvert(rmbs
                .getReferencePrefix());
        final ProgramElementName methodName = convert(rmbs.getMethodName());

        final ASTList<recoder.java.Expression> args = rmbs.getArguments();
        final Expression[] keyArgs;
        if (args != null) {
            keyArgs = new Expression[args.size()];
            for (int i = 0, sz = args.size(); i < sz; i++) {
                keyArgs[i] = (Expression) callConvert(args.get(i));
            }
        } else {
            keyArgs = new Expression[0];
        }

        final MethodReference mr = new MethodReference(new ArrayOfExpression(
                keyArgs), methodName, invocationTarget);

        return new MethodBodyStatement(bodySource, resultVar, mr);
    }
    
    public CatchAllStatement convert
        (de.uka.ilkd.key.java.recoderext.CatchAllStatement cas) {
        return new CatchAllStatement
            ((StatementBlock)callConvert(cas.getStatementAt(0)),
             (ParameterDeclaration) callConvert(cas.getParameterDeclarationAt(0)));
    }

    // ------------------- declaration ---------------------
    
    /** convert a recoder ClassDeclaration to a KeY ClassDeclaration */
    public ClassDeclaration convert(
            recoder.java.declaration.ClassDeclaration td) {

        KeYJavaType kjt = getKeYJavaType(td);
        ExtList classMembers = collectChildren(td);

        ClassDeclaration keYClassDecl = new ClassDeclaration(classMembers,
                new ProgramElementName(makeAdmissibleName(td.getFullName())),
                isParsingLibs(), td.getContainingClassType() != null,
                td.getName() == null, td.getStatementContainer() != null);
                // new ProgramElementName(td.getFullName()), isParsingLibs());

        kjt.setJavaType(keYClassDecl);
        return keYClassDecl;
    }

    /**
     * convert a recoder EnumDeclaration to a KeY EnumClassDeclaration. Enums
     * have already been mapped to classes at an earlier stage
     * 
     * @author m.u.
     */

    /*
     * // has to be reinserted when java5 is supported
     * 
     * public EnumClassDeclaration convert(
     * de.uka.ilkd.key.java.recoderext.EnumClassDeclaration td) {
     * 
     * KeYJavaType kjt = getKeYJavaType(td); ExtList classMembers =
     * collectChildren(td);
     * 
     * EnumClassDeclaration keyEnumDecl = new EnumClassDeclaration(
     * classMembers, new ProgramElementName(td.getFullName()), parsingLibs,
     * td.getEnumConstantDeclarations());
     * 
     * kjt.setJavaType(keyEnumDecl); return keyEnumDecl; }
     */

    public InterfaceDeclaration convert(
            recoder.java.declaration.InterfaceDeclaration td) {

        KeYJavaType kjt = getKeYJavaType(td);
        ExtList members = collectChildren(td);
        InterfaceDeclaration keYInterfaceDecl = new InterfaceDeclaration(
                members, new ProgramElementName(td.getFullName()),
                isParsingLibs());
        kjt.setJavaType(keYInterfaceDecl);

        return keYInterfaceDecl;
    }

    /**
     * converts a recoder ParameterDeclaration to a KeY ParameterDeclaration
     * (especially the declaration type of its parent is determined and handed
     * over)
     */
    public ParameterDeclaration convert(
            recoder.java.declaration.ParameterDeclaration pd) {
        return new ParameterDeclaration(
                collectChildren(pd),
                pd.getASTParent() instanceof recoder.java.declaration.InterfaceDeclaration,
                pd.isVarArg());
    }

    /**
     * convert a recoder FieldDeclaration to a KeY FieldDeclaration (especially
     * the declaration type of its parent is determined and handed over)
     */
    public FieldDeclaration convert(
            recoder.java.declaration.FieldDeclaration fd) {
        return new FieldDeclaration(
                collectChildren(fd),
                fd.getASTParent() instanceof recoder.java.declaration.InterfaceDeclaration);
    }

    /**
     * convert a recoder ConstructorDeclaration to a KeY ProgramMethod
     * (especially the declaration type of its parent is determined and handed
     * over)
     */
    public ProgramMethod convert(
            recoder.java.declaration.ConstructorDeclaration cd) {
        ConstructorDeclaration consDecl = new ConstructorDeclaration(
                collectChildren(cd),
                cd.getASTParent() instanceof recoder.java.declaration.InterfaceDeclaration);
        recoder.abstraction.ClassType cont = getServiceConfiguration()
        .getCrossReferenceSourceInfo().getContainingClassType(
                (recoder.abstraction.Member) cd);

        ProgramMethod result = new ProgramMethod(consDecl,
                getKeYJavaType(cont), getKeYJavaType(cd.getReturnType()),
                positionInfo(cd));
        insertToMap(cd, result);
        return result;
    }

    /**
     * convert a recoder DefaultConstructor to a KeY ProgramMethod (especially
     * the declaration type of its parent is determined and handed over)
     */
    public ProgramMethod convert(recoder.abstraction.DefaultConstructor dc) {
        ExtList children = new ExtList();
        children.add(new ProgramElementName(dc.getName()));
        ConstructorDeclaration consDecl = new ConstructorDeclaration(children,
                dc.getContainingClassType().isInterface());
        recoder.abstraction.ClassType cont = dc.getContainingClassType();
        ProgramMethod result = new ProgramMethod(consDecl,
                getKeYJavaType(cont), getKeYJavaType(dc.getReturnType()),
                PositionInfo.UNDEFINED);
        insertToMap(dc, result);
        return result;
    }

    /** convert a recoder type cast to a KeY TypeCast */
    public TypeCast convert(recoder.java.expression.operator.TypeCast c) {
        return new TypeCast((Expression) callConvert(c.getExpressionAt(0)),
                (TypeReference) callConvert(c.getTypeReference()));
    }

    /**
     * converts a SpecialConstructorReference. Special handling because the
     * initializing Expressions and the ReferencePrefix accessPath might not be
     * disjunct.
     */
    public SuperConstructorReference convert(
            recoder.java.reference.SuperConstructorReference scr) {

        ExtList children = collectChildren(scr);
        ReferencePrefix prefix = null;
        int prefixPos = scr.getIndexOfChild(scr.getReferencePrefix());
        if (prefixPos != -1) {
            prefix = (ReferencePrefix) children.get(prefixPos);
            children.remove(prefixPos);
        }
        return new SuperConstructorReference(children, prefix);
    }

    /**
     * Convert a this referene. Special handling because the initializing
     * Expressions and the ReferencePrefix accessPath might not be disjunct.
     */
    public ThisReference convert(recoder.java.reference.ThisReference tr) {

        ExtList children = collectChildren(tr);
        ReferencePrefix prefix = null;

        int prefixPos = tr.getIndexOfChild(tr.getReferencePrefix());
        if (prefixPos != -1) {
            prefix = (ReferencePrefix) children.get(prefixPos);
            children.remove(prefixPos);
        }
        return new ThisReference((TypeReference) prefix);
    }

    /**
     * Convert a super referene. Special handling because the initializing
     * Expressions and the ReferencePrefix accessPath might not be disjunct.
     */
    public SuperReference convert(recoder.java.reference.SuperReference sr) {

        ExtList children = collectChildren(sr);

        int prefixPos = sr.getIndexOfChild(sr.getReferencePrefix());
        if (prefixPos != -1) {
            children.remove(prefixPos);
        }

        return new SuperReference(children);
    }

    /**
     * convert a recoder VariableSpecification to a KeY VariableSpecification
     * (checks dimension and hands it over and insert in hashmap)
     */
    public VariableSpecification convert(
            recoder.java.declaration.VariableSpecification recoderVarSpec) {

        VariableSpecification varSpec = (VariableSpecification) getMapping()
        .toKeY(recoderVarSpec);

        if (varSpec == null) {
            recoder.abstraction.Type recoderType = (getServiceConfiguration()
                    .getSourceInfo()).getType(recoderVarSpec);

            final ProgramElementName name = VariableNamer
                    .parseName(makeAdmissibleName(recoderVarSpec.getName()));
            final ProgramVariable pv = new LocationVariable(name,
                    getKeYJavaType(recoderType), recoderVarSpec.isFinal());
            varSpec = new VariableSpecification(
                    collectChildren(recoderVarSpec), pv, recoderVarSpec
                    .getDimensions(), pv.getKeYJavaType());

            insertToMap(recoderVarSpec, varSpec);
        }
        return varSpec;
    }

    /**
     * convert a recoder MethodDeclaration to a KeY ProgramMethod (especially
     * the declaration type of its parent is determined and handed over)
     */
    public ProgramMethod convert(recoder.java.declaration.MethodDeclaration md) {
        ProgramMethod result = null;

        // methodsDeclaring contains the recoder method declarations as keys
        // that have been started to convert but are not yet finished.
        // The mapped value is the reference to the later completed
        // ProgramMethod.
        if (methodsDeclaring.containsKey(md)) {
            // a recursive call from a method reference
            return (ProgramMethod) methodsDeclaring.get(md);
            // reference that will later be set.
        }

        methodsDeclaring.put(md, result);
        if (!getMapping().mapped(md)) {
            final MethodDeclaration methDecl = new MethodDeclaration(
                    collectChildren(md),
                    md.getASTParent() instanceof recoder.java.declaration.InterfaceDeclaration);
            recoder.abstraction.ClassType cont = getServiceConfiguration()
            .getCrossReferenceSourceInfo().getContainingClassType(
                    (recoder.abstraction.Member) md);

            result = new ProgramMethod(methDecl, getKeYJavaType(cont),
                    getKeYJavaType(md.getReturnType()), positionInfo(md));

            insertToMap(md, result);
        }
        methodsDeclaring.remove(md);
        result = (ProgramMethod) getMapping().toKeY(md);
        return result;
    }

    /**
     * convert a recoder FieldSpecification to a KeY FieldSpecification (checks
     * dimension and hands it over and insert in hash map)
     */
    public FieldSpecification convert(
            recoder.java.declaration.FieldSpecification recoderVarSpec) {

        if (recoderVarSpec == null) { // %%%%%%%%%%%%%
            return new FieldSpecification();
        }

        FieldSpecification varSpec = (FieldSpecification) getMapping().toKeY(
                recoderVarSpec);

        if (varSpec == null) {
            recoder.abstraction.Type recoderType = (getServiceConfiguration()
                    .getSourceInfo()).getType(recoderVarSpec);

            ProgramVariable pv = getProgramVariableForFieldSpecification(recoderVarSpec);

            if (recoderVarSpec.getIdentifier() instanceof ImplicitIdentifier) {
                // the modelled field is an implicit one, we have to handle this
                // one
                // explicit
                varSpec = new ImplicitFieldSpecification(pv,
                        getKeYJavaType(recoderType));
            } else {
                varSpec = new FieldSpecification(
                        collectChildren(recoderVarSpec), pv, recoderVarSpec
                        .getDimensions(), getKeYJavaType(recoderType));
            }
            insertToMap(recoderVarSpec, varSpec);
        }

        return varSpec;
    }

    /**
     * this is needed by #convert(FieldSpecification).
     */
    private ProgramVariable getProgramVariableForFieldSpecification(
            recoder.java.declaration.FieldSpecification recoderVarSpec) {

        if (recoderVarSpec == null) {
            return null;
        }

        ProgramVariable pv = (ProgramVariable) fieldSpecificationMapping
        .get(recoderVarSpec);

        if (pv == null) {
            VariableSpecification varSpec = (VariableSpecification) getMapping()
            .toKeY(recoderVarSpec);
            if (varSpec == null) {
                recoder.abstraction.Type recoderType = (getServiceConfiguration()
                        .getSourceInfo()).getType(recoderVarSpec);
                final ClassType recContainingClassType = recoderVarSpec
                .getContainingClassType();
                final ProgramElementName pen = new ProgramElementName(
                        makeAdmissibleName(recoderVarSpec.getName()), 
                        makeAdmissibleName(recContainingClassType.getFullName()));

                final Literal compileTimeConstant = getCompileTimeConstantInitializer(recoderVarSpec);

                if (compileTimeConstant == null) {
                    pv = new LocationVariable(pen, getKeYJavaType(recoderType),
                            getKeYJavaType(recContainingClassType),
                            recoderVarSpec.isStatic());
                } else {
                    pv = new ProgramConstant(pen, getKeYJavaType(recoderType),
                            getKeYJavaType(recContainingClassType),
                            recoderVarSpec.isStatic(), compileTimeConstant);
                }
            } else {
                pv = (ProgramVariable) varSpec.getProgramVariable();
            }
            fieldSpecificationMapping.put(recoderVarSpec, pv);
        }

        return pv;
    }

    /**
     * needed by
     * {@link #getProgramVariableForFieldSpecification(recoder.java.declaration.FieldSpecification)}.
     * 
     * @return a literal constant representing the value of the initializer of
     *         <code>recoderVarSpec</code>, if the variable is a compile-time
     *         constant, and <code>null</code> otherwise
     */
    private Literal getCompileTimeConstantInitializer(
            recoder.java.declaration.FieldSpecification recoderVarSpec) {

        // Necessary condition: the field is static and final
        if (!recoderVarSpec.isFinal() || !recoderVarSpec.isStatic())
            return null;

        recoder.java.Expression init = recoderVarSpec.getInitializer();

        if (init != null) {
            recoder.service.ConstantEvaluator ce = new recoder.service.DefaultConstantEvaluator(
                    getServiceConfiguration());
            recoder.service.ConstantEvaluator.EvaluationResult er = new recoder.service.ConstantEvaluator.EvaluationResult();

            if (ce.isCompileTimeConstant(init, er))
                return getLiteralFor(er);
        }

        return null;
    }

    /**
     * convert a recoder TypeReference to a KeY TypeReference (checks dimension
     * and hands it over)
     */
    public TypeReference convert(recoder.java.reference.TypeReference tr) {

        recoder.abstraction.Type rType = getServiceConfiguration().getSourceInfo().getType(tr);

        if (rType == null)
            return null; // because of 'void'

        KeYJavaType kjt = getKeYJavaType(rType);
        ExtList children = collectChildren(tr);
        TypeReference result = new TypeRef(children, kjt, tr.getDimensions());
        return result;
    }

    /**
     * if an UncollatedReferenceQualifier appears throw a ConvertExceception
     * because these qualifiers have to be resolved by running the
     * CrossReferencer
     */
    public ProgramElement convert(
            recoder.java.reference.UncollatedReferenceQualifier urq) {
        recoder.java.ProgramElement pe = getServiceConfiguration()
        .getCrossReferenceSourceInfo().resolveURQ(urq);
        if (pe != null
                && !(pe instanceof recoder.java.reference.UncollatedReferenceQualifier)) {
            return (ProgramElement) callConvert(pe);
        }
        throw new PosConvertException("recoder2key: Qualifier " + urq.getName()
                + " not resolvable.", urq.getFirstElement().getStartPosition()
                .getLine(), urq.getFirstElement().getStartPosition()
                .getColumn() - 1);
    }

    /**
     * this is needed to convert variable references
     */
    private recoder.java.declaration.VariableSpecification getRecoderVarSpec(
            recoder.java.reference.VariableReference vr) {
        return getServiceConfiguration().getSourceInfo()
        .getVariableSpecification(
                getServiceConfiguration().getSourceInfo().getVariable(
                        vr));
    }

    /**
     * converts a recoder variable reference. A ProgramVariable is created
     * replacing the variable reference.
     * 
     * @param vr
     *            the recoder variable reference.
     */
    public ProgramVariable convert(recoder.java.reference.VariableReference vr) {

        final recoder.java.declaration.VariableSpecification recoderVarspec = getRecoderVarSpec(vr);

        if (!getMapping().mapped(recoderVarspec)) {
            insertToMap(recoderVarspec, convert(recoderVarspec));
        }

        return (ProgramVariable) ((VariableSpecification) getMapping().toKeY(
                recoderVarspec)).getProgramVariable();
    }

    /**
     * converts a recoder array length reference to a usual KeY field reference
     */
    public FieldReference convert(
            recoder.java.reference.ArrayLengthReference alr) {
        recoder.abstraction.Type recoderType = getServiceConfiguration()
        .getCrossReferenceSourceInfo()
        .getType(alr.getReferencePrefix());
        ArrayDeclaration ad = (ArrayDeclaration) getKeYJavaType(recoderType)
        .getJavaType();

        final ProgramVariable length = find("length", filterField(ad.length()));
        // the invocation of callConvert should work well as each array
        // length reference must have a reference prefix (at least this
        // is what i think)
        return new FieldReference(length, (ReferencePrefix) callConvert(alr
                .getReferencePrefix()));
    }

    /**
     * converts a recoder field reference. A ProgramVariable is created
     * replacing the field reference.
     * 
     * @param fr
     *            the recoder field reference.
     */
    public Expression convert(recoder.java.reference.FieldReference fr) {
        ProgramVariable pv;

        recoder.java.declaration.FieldSpecification recoderVarSpec = (recoder.java.declaration.FieldSpecification) getRecoderVarSpec(fr);

        ReferencePrefix prefix = null;

        if (fr.getReferencePrefix() != null) {
            prefix = (ReferencePrefix) callConvert(fr.getReferencePrefix());
        }

        if (recoderVarSpec == null) {
            // null means only bytecode available for this
            // field %%%
            recoder.abstraction.Field recField = getServiceConfiguration()
            .getSourceInfo().getField(fr);
            recoder.abstraction.Type recoderType = getServiceConfiguration()
            .getByteCodeInfo().getType(recField);
            recoder.java.declaration.FieldSpecification fs = new recoder.java.declaration.FieldSpecification(
                    fr.getIdentifier());
            pv = new LocationVariable(new ProgramElementName(makeAdmissibleName(fs.getName()),
                    makeAdmissibleName(recField.getContainingClassType().getFullName())),
                    getKeYJavaType(recoderType), getKeYJavaType(recField
                            .getContainingClassType()), recField.isStatic());
            insertToMap(fs, new FieldSpecification(pv));
            return new FieldReference(pv, prefix);
        }

        pv = getProgramVariableForFieldSpecification(recoderVarSpec);

        if (!pv.isMember()) {
            // in case of a cut, induction rule or s.th. else recoder will
            // resolve
            // all variables of the created context as field references but
            // in fact they are references to local variables, so we have
            // to fix it here
            // same applies for variables declared in program variables
            // section
            return pv;
        }

        return new FieldReference(pv, prefix);
    }

    /**
     * converts a recoder method reference. A
     * de.uka.ilkd.key.logic.op.ProgramMethod is created replacing the method
     * reference.
     * 
     * @param mr
     *            the recoder method reference.
     * @return the Method the KeY Dependance
     */
    public MethodReference convert(recoder.java.reference.MethodReference mr) {
        recoder.service.SourceInfo sourceInfo = getServiceConfiguration()
        .getSourceInfo();
        recoder.abstraction.Method method = sourceInfo.getMethod(mr);

        final ProgramMethod pm;
        if (!getMapping().mapped(method)) {
            if (method instanceof recoder.java.declaration.MethodDeclaration) {
                // method reference before method decl, also recursive calls.
                // do not use:
                final String oldCurrent = currentClass;
                final String className = ((recoder.java.declaration.MethodDeclaration) method)
                .getMemberParent().getFullName();
                recoder.io.DataLocation loc = getServiceConfiguration()
                .getSourceFileRepository().findSourceFile(className);
                if (loc instanceof recoder.io.DataFileLocation) {
                    currentClass = ((recoder.io.DataFileLocation) loc)
                    .getFile().getAbsolutePath();
                } else {
                    currentClass = (loc == null ? null : "" + loc);
                }
                pm = convert((recoder.java.declaration.MethodDeclaration) method);
                // because of cycles when reading recursive programs
                currentClass = oldCurrent;
            } else {
                // bytecode currently we do nothing
                pm = null;
            }
        } else {
            pm = (ProgramMethod) getMapping().toKeY(method);
        }

        ExtList children = collectChildren(mr);
        // convert reference prefix separately
        ReferencePrefix prefix = null;
        int prefixPos = mr.getIndexOfChild(mr.getReferencePrefix());
        if (prefixPos != -1) {
            prefix = (ReferencePrefix) children.get(prefixPos);
            children.remove(prefixPos);
        }

        return new MethodReference(children,
                pm == null ? new ProgramElementName(mr.getName()) : pm
                        .getProgramElementName(), prefix, positionInfo(mr));
    }

    // --------------Special treatment because of ambiguities ----------

    /**
     * convert a labeled statement. Remove the label from the set of children
     * and pass it separately.
     */
    public LabeledStatement convert(recoder.java.statement.LabeledStatement l) {
        ExtList children = collectChildren(l);
        Label lab = null;
        int labPos = l.getIndexOfChild(l.getIdentifier());
        if (labPos != -1) {
            lab = (Label) children.get(labPos);
            children.remove(labPos);
        }
        return new LabeledStatement(children, lab, positionInfo(l));
    }

    /**
     * converts a For.
     * 
     * @param f
     *            the For of recoder
     * @return the For of KeY
     */
    public For convert(recoder.java.statement.For f) {
        return new For(convertLoopInitializers(f), convertGuard(f),
                convertUpdates(f), convertBody(f), collectComments(f),
                positionInfo(f));
    }

    /**
     * converts a java5-enhanced-for.
     * 
     * @param f
     *            the EnhancedFor of recoder
     * @return the EnhancedFor of KeY
     */
    
     public EnhancedFor convert(recoder.java.statement.EnhancedFor f) { 
         return new EnhancedFor(convertLoopInitializers(f), convertGuard(f),
                 convertBody(f),collectComments(f),positionInfo(f)); 
     }
     

    /**
     * converts a While.
     * 
     * @param w
     *            the While of recoder
     * @return the While of KeY
     */
    public While convert(recoder.java.statement.While w) {
        return new While(convertGuard(w).getExpression(), convertBody(w),
                positionInfo(w), collectComments(w));
    }

    /**
     * converts a Do.
     * 
     * @param d
     *            the Do of recoder
     * @return the Do of KeY
     */
    public Do convert(recoder.java.statement.Do d) {
        return new Do(convertGuard(d).getExpression(), convertBody(d),
                collectComments(d), positionInfo(d));
    }

    /**
     * helper for convert(x) with x a LoopStatement. Converts the body of x.
     */
    public Statement convertBody(recoder.java.statement.LoopStatement ls) {
        Object body = null;
        if (ls.getBody() != null) {
            body = callConvert(ls.getBody());
        }
        return (Statement) body;
    }

    /**
     * helper for convert(x) with x a LoopStatement. Converts the guard of x.
     */
    public Guard convertGuard(recoder.java.statement.LoopStatement ls) {
        Object guard = null;
        if (ls.getGuard() != null) {
            guard = callConvert(ls.getGuard());
        }
        return new Guard((Expression) guard);
    }

    /**
     * helper for convert(x) with x a LoopStatement. Converts the updates of x.
     */
    public ForUpdates convertUpdates(recoder.java.statement.LoopStatement ls) {
        final ExtList updates = new ExtList();
        ASTList<recoder.java.Expression> recLoopUpdates = ls.getUpdates();
        inLoopInit = true;
        if (recLoopUpdates != null) {
            for (int i = 0, sz = recLoopUpdates.size(); i < sz; i++) {
                updates.add(callConvert(recLoopUpdates.get(i)));
            }
            inLoopInit = false;
            return new ForUpdates(updates, positionInfo(ls));
        }
        return null;
    }

    /**
     * helper for convert(x) with x a LoopStatement. Converts the loop
     * initializers of x.
     */
    public LoopInit convertLoopInitializers(
            recoder.java.statement.LoopStatement ls) {

        final LoopInit loopInit;

        ASTList<recoder.java.LoopInitializer> initializers = ls.getInitializers();
        if (initializers != null) {
            final LoopInitializer[] result = new LoopInitializer[initializers
                                                                 .size()];
            for (int i = 0, sz = initializers.size(); i < sz; i++) {
                inLoopInit = true;
                result[i] = (LoopInitializer) callConvert(initializers
                        .get(i));
                inLoopInit = false;
            }
            loopInit = new LoopInit(result);
        } else {
            loopInit = null;
        }
        return loopInit;
    }

    /**
     * converts an ArrayReference. Special handling because the initializing
     * Expressions and the ReferencePrefix accessPath might not be disjunct.
     */
    public ArrayReference convert(recoder.java.reference.ArrayReference ar) {
        ExtList children = collectChildren(ar);
        ReferencePrefix prefix = null;

        int prefixPos = ar.getIndexOfChild(ar.getReferencePrefix());
        if (prefixPos != -1) {
            prefix = (ReferencePrefix) children.get(prefixPos);
            children.remove(prefixPos);
        }
        return new ArrayReference(children, prefix);
    }

    /** convert Assert */
    public Assert convert(recoder.java.statement.Assert a) {
        final Expression message;
        if (a.getMessage() != null) {
            message = (Expression) callConvert(a.getMessage());
        } else {
            message = null;
        }
        return new Assert((Expression) callConvert(a.getCondition()), message,
                positionInfo(a));
    }

    /**
     * converts a Case. Special handling because the initializing Expression and
     * Statements might not be disjunct.
     */
    public Case convert(recoder.java.statement.Case c) {
        ExtList children = collectChildren(c);
        Expression expr = null;
        int exprPos = c.getIndexOfChild(c.getExpression());
        if (exprPos != -1) {
            expr = (Expression) children.get(exprPos);
            children.remove(exprPos);
        }
        return new Case(children, expr, positionInfo(c));
    }

    /**
     * converts a New. Special handling because the ReferencePrefix and the
     * TypeReference might not be disjunct.
     */
    public New convert(recoder.java.expression.operator.New n) {

        ASTList<recoder.java.Expression> args = n.getArguments();
        final recoder.java.reference.ReferencePrefix rp = n
        .getReferencePrefix();
        final recoder.java.reference.TypeReference tr = n.getTypeReference();
        final recoder.java.declaration.ClassDeclaration cd = n.getClassDeclaration();
        
        LinkedList outerVars = null;
        if(locClass2finalVar != null){
            outerVars = (LinkedList) locClass2finalVar.get(cd);
        }
        
        int numVars = outerVars!=null? outerVars.size() : 0;
        Expression[] arguments = new Expression[(args != null ? args.size() : 0)+numVars];
        for (int i = 0; i < arguments.length-numVars; i++) {
            arguments[i] = (Expression)callConvert(args.get(i));
        }
        
        for (int i = arguments.length-numVars; i<arguments.length; i++) {
            arguments[i] = (ProgramVariable) convert(
                    (recoder.java.declaration.VariableSpecification)
                        outerVars.get(i-arguments.length + numVars)).getProgramVariable();
        }
        
        TypeReference maybeAnonClass = (TypeReference) callConvert(tr);
        if(n.getClassDeclaration() != null){
            callConvert(n.getClassDeclaration());
            KeYJavaType kjt = getKeYJavaType(n.getClassDeclaration());
            maybeAnonClass = new TypeRef(kjt);
        }

        if (rp == null) {
            return new New(arguments, maybeAnonClass,
                    (ReferencePrefix) null);
        } else {
            return new New(arguments, maybeAnonClass,
                    (ReferencePrefix) callConvert(rp));
        }
    }

    public Import convert(recoder.java.Import im) {
        return new Import(collectChildren(im), im.isMultiImport());
    }
    
    /**
     * convert a statement block and remove all included anonymous classes.
     * @param block the recoder.java.StatementBlock to be converted
     * @return the converted StatementBlock
     */
    public StatementBlock convert(recoder.java.StatementBlock block) {
        ExtList children = collectChildrenAndComments(block);
        
        // remove local classes
        while (children.removeFirstOccurrence(ClassDeclaration.class) != null) {
            // do nothing
        }
        return new StatementBlock(children);

    }

    // ----- Default behaviour


    public PassiveExpression convert(de.uka.ilkd.key.java.recoderext.PassiveExpression arg) {
        return new PassiveExpression(collectChildrenAndComments(arg));
    }

    public ParenthesizedExpression convert(recoder.java.expression.ParenthesizedExpression arg) {
        return new ParenthesizedExpression(collectChildrenAndComments(arg));
    }

    public CopyAssignment convert(recoder.java.expression.operator.CopyAssignment arg) {
        return new CopyAssignment(collectChildrenAndComments(arg));
    }

    public SetAssignment convert(de.uka.ilkd.key.java.recoderext.SetAssignment ass){ 
        return new SetAssignment(collectChildren(ass));
    }

    public PostIncrement convert(recoder.java.expression.operator.PostIncrement arg) {
        return new PostIncrement(collectChildrenAndComments(arg));
    }

    public PreIncrement convert(recoder.java.expression.operator.PreIncrement arg) {
        return new PreIncrement(collectChildrenAndComments(arg));
    }

    public PostDecrement convert(recoder.java.expression.operator.PostDecrement arg) {
        return new PostDecrement(collectChildrenAndComments(arg));
    }

    public PreDecrement convert(recoder.java.expression.operator.PreDecrement arg) {
        return new PreDecrement(collectChildrenAndComments(arg));
    }

    public Minus convert(recoder.java.expression.operator.Minus arg) {
        return new Minus(collectChildrenAndComments(arg));
    }

    public Plus convert(recoder.java.expression.operator.Plus arg) {
        return new Plus(collectChildrenAndComments(arg));
    }

    public Times convert(recoder.java.expression.operator.Times arg) {
        return new Times(collectChildrenAndComments(arg));
    }

    public Divide convert(recoder.java.expression.operator.Divide arg) {
        return new Divide(collectChildrenAndComments(arg));
    }

    public PlusAssignment convert(recoder.java.expression.operator.PlusAssignment arg) {
        return new PlusAssignment(collectChildrenAndComments(arg));
    }

    public MinusAssignment convert(recoder.java.expression.operator.MinusAssignment arg) {
        return new MinusAssignment(collectChildrenAndComments(arg));
    }

    public TimesAssignment convert(recoder.java.expression.operator.TimesAssignment arg) {
        return new TimesAssignment(collectChildrenAndComments(arg));
    }

    public DivideAssignment convert(recoder.java.expression.operator.DivideAssignment arg) {
        return new DivideAssignment(collectChildrenAndComments(arg));
    }

    public LessThan convert(recoder.java.expression.operator.LessThan arg) {
        return new LessThan(collectChildrenAndComments(arg));
    }

    public LessOrEquals convert(recoder.java.expression.operator.LessOrEquals arg) {
        return new LessOrEquals(collectChildrenAndComments(arg));
    }

    public GreaterThan convert(recoder.java.expression.operator.GreaterThan arg) {
        return new GreaterThan(collectChildrenAndComments(arg));
    }

    public GreaterOrEquals convert(recoder.java.expression.operator.GreaterOrEquals arg) {
        return new GreaterOrEquals(collectChildrenAndComments(arg));
    }

    public Equals convert(recoder.java.expression.operator.Equals arg) {
        return new Equals(collectChildrenAndComments(arg));
    }

    public NotEquals convert(recoder.java.expression.operator.NotEquals arg) {
        return new NotEquals(collectChildrenAndComments(arg));
    }

    public LogicalNot convert(recoder.java.expression.operator.LogicalNot arg) {
        return new LogicalNot(collectChildrenAndComments(arg));
    }

    public LogicalAnd convert(recoder.java.expression.operator.LogicalAnd arg) {
        return new LogicalAnd(collectChildrenAndComments(arg));
    }

    public LogicalOr convert(recoder.java.expression.operator.LogicalOr arg) {
        return new LogicalOr(collectChildrenAndComments(arg));
    }

    public ArrayInitializer convert(recoder.java.expression.ArrayInitializer arg) {
        return new ArrayInitializer(collectChildrenAndComments(arg));
    }

    public Throw convert(recoder.java.statement.Throw  arg) {
        return new Throw (collectChildrenAndComments(arg));
    }

    public If  convert(recoder.java.statement.If  arg) {
        return new If (collectChildrenAndComments(arg));
    }

    public Then  convert(recoder.java.statement.Then  arg) {
        return new Then (collectChildrenAndComments(arg));
    }

    public Else  convert(recoder.java.statement.Else  arg) {
        return new Else (collectChildrenAndComments(arg));
    }

    public SynchronizedBlock convert(recoder.java.statement.SynchronizedBlock arg) {
        return new SynchronizedBlock(collectChildrenAndComments(arg));
    }

    public Return convert(recoder.java.statement.Return arg) {
        return new Return(collectChildrenAndComments(arg));
    }

    public Try convert(recoder.java.statement.Try arg) {
        return new Try(collectChildrenAndComments(arg));
    }

    public Catch convert(recoder.java.statement.Catch arg) {
        return new Catch(collectChildrenAndComments(arg));
    }

    public Finally convert(recoder.java.statement.Finally arg) {
        return new Finally(collectChildrenAndComments(arg));
    }

    public CompilationUnit convert(recoder.java.CompilationUnit arg) {
        return new CompilationUnit(collectChildrenAndComments(arg));
    }

    public ClassInitializer convert(recoder.java.declaration.ClassInitializer arg) {
        return new ClassInitializer(collectChildrenAndComments(arg));
    }

    public PackageSpecification convert(recoder.java.PackageSpecification arg) {
        return new PackageSpecification(collectChildrenAndComments(arg));
    }

    public Throws convert(recoder.java.declaration.Throws arg) {
        return new Throws(collectChildrenAndComments(arg));
    }

    public Extends convert(recoder.java.declaration.Extends arg) {
        return new Extends(collectChildrenAndComments(arg));
    }

    public Implements convert(recoder.java.declaration.Implements arg) {
        return new Implements(collectChildrenAndComments(arg));
    }

    public LocalVariableDeclaration convert(recoder.java.declaration.LocalVariableDeclaration arg) {
        return new LocalVariableDeclaration(collectChildrenAndComments(arg));
    }

    public ExecutionContext convert(de.uka.ilkd.key.java.recoderext.ExecutionContext arg) {
        return new ExecutionContext(collectChildrenAndComments(arg));
    }

    public ThisConstructorReference convert(recoder.java.reference.ThisConstructorReference arg) {
        return new ThisConstructorReference(collectChildrenAndComments(arg));
    }

    public BinaryAnd convert(recoder.java.expression.operator.BinaryAnd arg) {
        return new BinaryAnd(collectChildrenAndComments(arg));
    }

    public BinaryOr convert(recoder.java.expression.operator.BinaryOr arg) {
        return new BinaryOr(collectChildrenAndComments(arg));
    }

    public BinaryXOr convert(recoder.java.expression.operator.BinaryXOr arg) {
        return new BinaryXOr(collectChildrenAndComments(arg));
    }

    public BinaryNot convert(recoder.java.expression.operator.BinaryNot arg) {
        return new BinaryNot(collectChildrenAndComments(arg));
    }

    public BinaryAndAssignment convert(recoder.java.expression.operator.BinaryAndAssignment arg) {
        return new BinaryAndAssignment(collectChildrenAndComments(arg));
    }

    public BinaryOrAssignment convert(recoder.java.expression.operator.BinaryOrAssignment arg) {
        return new BinaryOrAssignment(collectChildrenAndComments(arg));
    }

    public BinaryXOrAssignment convert(recoder.java.expression.operator.BinaryXOrAssignment arg) {
        return new BinaryXOrAssignment(collectChildrenAndComments(arg));
    }

    public ShiftLeft convert(recoder.java.expression.operator.ShiftLeft arg) {
        return new ShiftLeft(collectChildrenAndComments(arg));
    }

    public ShiftRight convert(recoder.java.expression.operator.ShiftRight arg) {
        return new ShiftRight(collectChildrenAndComments(arg));
    }

    public UnsignedShiftRight convert(recoder.java.expression.operator.UnsignedShiftRight arg) {
        return new UnsignedShiftRight(collectChildrenAndComments(arg));
    }

    public ShiftLeftAssignment convert(recoder.java.expression.operator.ShiftLeftAssignment arg) {
        return new ShiftLeftAssignment(collectChildrenAndComments(arg));
    }

    public ShiftRightAssignment convert(recoder.java.expression.operator.ShiftRightAssignment arg) {
        return new ShiftRightAssignment(collectChildrenAndComments(arg));
    }

    public UnsignedShiftRightAssignment convert(recoder.java.expression.operator.UnsignedShiftRightAssignment arg) {
        return new UnsignedShiftRightAssignment(collectChildrenAndComments(arg));
    }

    public Negative convert(recoder.java.expression.operator.Negative arg) {
        return new Negative(collectChildrenAndComments(arg));
    }

    public Positive convert(recoder.java.expression.operator.Positive arg) {
        return new Positive(collectChildrenAndComments(arg));
    }

    public Modulo convert(recoder.java.expression.operator.Modulo arg) {
        return new Modulo(collectChildrenAndComments(arg));
    }

    public ModuloAssignment convert(recoder.java.expression.operator.ModuloAssignment arg) {
        return new ModuloAssignment(collectChildrenAndComments(arg));
    }

    public Conditional convert(recoder.java.expression.operator.Conditional arg) {
        return new Conditional(collectChildrenAndComments(arg));
    }

    public Break convert(recoder.java.statement.Break arg) {
        return new Break(collectChildrenAndComments(arg));
    }

    public Ghost convert(de.uka.ilkd.key.java.recoderext.Ghost m) {
        return new Ghost(collectComments(m));
    }

    public Model convert(de.uka.ilkd.key.java.recoderext.Model m) {
        return new Model(collectComments(m));
    }


}	

