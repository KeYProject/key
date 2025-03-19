/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URI;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;

import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.*;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.*;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.recoderext.ImplicitIdentifier;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Type;
import recoder.io.DataLocation;
import recoder.java.NonTerminalProgramElement;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.declaration.TypeDeclaration;
import recoder.list.generic.ASTList;

import static java.lang.String.format;

/**
 * Objects of this class can be used to transform an AST returned by the recoder library to the
 * corresponding yet immutable KeY data structures.
 * <p>
 * Call the method process() to convert an arbitrary object.
 * <p>
 * The method callConvert is used to perform a run-time dispatch upon the parameters.
 * <p>
 * The actual conversion is done in convert-methods which must be declared public due to the used
 * reflection method lookup function.
 * <p>
 * There is a general method {@link #callConvert(recoder.java.ProgramElement)} that does the job in
 * general. Several special cases must be treated separately.
 * <p>
 * This code used to be part of {@link Recoder2KeY} and has been 'out-sourced'.
 *
 * @author mattias ulbrich
 * @since Jul-07
 */
public class Recoder2KeYConverter {
    private static final Logger LOGGER = LoggerFactory.getLogger(Recoder2KeYConverter.class);

    // -------- public part

    private final Services services;

    public ProgramElement process(recoder.java.ProgramElement pe) {
        Object result = callConvert(pe);
        assert result instanceof ProgramElement : "result must be a ProgramElement";
        return (ProgramElement) result;
    }

    public IProgramMethod processDefaultConstructor(recoder.abstraction.DefaultConstructor df) {
        return convert(df);
    }

    public CompilationUnit processCompilationUnit(recoder.java.CompilationUnit cu,
            DataLocation context) {
        currentClassURI = MiscTools.extractURI(context).orElse(null);
        Object result = process(cu);
        currentClassURI = null;

        assert result instanceof CompilationUnit
                : "a compilation unit must result in a compilation unit!";

        return (CompilationUnit) result;
    }

    public Recoder2KeYConverter(Recoder2KeY rec2key, Services services, NamespaceSet nss) {
        super();
        this.rec2key = rec2key;
        this.services = services;
        this.namespaceSet = nss;
    }

    // -------- implementation part

    /**
     * caches access to methods for reflection. It is a HashMap<Class, Method>
     */
    private final HashMap<Class<?>, Method> methodCache = new LinkedHashMap<>(400);

    /**
     * caches constructor access for reflection. It is a HashMap<Class, Constructor>
     */
    private final HashMap<Class<? extends recoder.java.JavaProgramElement>, Constructor<?>> constructorCache =
        new LinkedHashMap<>(400);

    /**
     * Hashmap from <code>recoder.java.declaration.FieldSpecification</code> to
     * <code>ProgramVariable</code>; this is necessary to avoid cycles when converting initializers.
     * Access to this map is performed via the method
     * <code>getProgramVariableForFieldSpecification</code>
     */
    private final HashMap<recoder.java.declaration.FieldSpecification, ProgramVariable> fieldSpecificationMapping =
        new LinkedHashMap<>();

    /**
     * methodsDeclaring contains the recoder method declarations as keys that have been started to
     * convert but are not yet finished. The mapped value is the reference to the later completed
     * IProgramMethod.
     */
    private final HashMap<recoder.java.declaration.MethodDeclaration, IProgramMethod> methodsDeclaring =
        new LinkedHashMap<>();

    /**
     * locClass2finalVar stores the final variables that need to be passed to the constructor of an
     * anonymous class.
     */
    protected Map<?, ?> locClass2finalVar = null;

    /**
     * stores the URI of the class that is currently processed
     */
    private URI currentClassURI;

    /**
     * flag which is true if currently in a for initialiser or update
     */
    private boolean inLoopInit = false;

    /**
     * the associated Recoder2KeY object
     */
    private final Recoder2KeY rec2key;

    /**
     * The namespaces are here to provide some conversion functions access to previously defined
     * logical symbols.
     */
    private final NamespaceSet namespaceSet;

    /**
     * retrieve a key type using the converter available from Recoder2KeY
     *
     * @param javaType type to look up
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
     * retrieve the recoder {@code <->} key mapping from the associated Recoder2KeY.
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
     * convert a recoder ProgramElement to a corresponding KeY data structure entity.
     * <p>
     * Almost always the returned type carries the same Classname but in a KeY rather than a recoder
     * package.
     * <p>
     * Determines the right convert method using reflection
     *
     * @param pe the recoder.java.JavaProgramElement to be converted, not null.
     *
     * @return the converted element
     *
     * @throws ConvertException if the conversion fails
     */
    protected Object callConvert(recoder.java.ProgramElement pe) throws ConvertException {

        if (pe == null) {
            throw new ConvertException("cannot convert 'null'");
        }

        Class<?> contextClass = pe.getClass();
        Method m = methodCache.get(contextClass);

        // if not in cache, search it - and fill the cache
        if (m == null) {
            Class<?>[] context = new Class<?>[] { contextClass };

            // remember all superclasses for the cache
            LinkedList<Class<?>> l = new LinkedList<>();

            while (m == null && context[0] != null) {
                l.add(contextClass);

                try {
                    m = getClass().getMethod("convert", context);
                } catch (NoSuchMethodException nsme) {
                    context[0] = contextClass = context[0].getSuperclass();
                }
            }

            if (m == null) {
                throw new ConvertException(
                    "Could not find convert method for class or superclasses of " + pe.getClass());
            }

            for (Class<?> aL : l) {
                methodCache.put(aL, m);
            }
        }

        // method found - now make the call to it.

        Object result = null;
        try {
            result = m.invoke(this, pe);
        } catch (IllegalAccessException iae) {
            LOGGER.debug("recoder2key: cannot access method ", iae);
            throw new ConvertException("recoder2key: cannot access method", iae);
        } catch (IllegalArgumentException iarg) {
            LOGGER.debug("recoder2key: wrong method arguments ", iarg);
            throw new ConvertException("recoder2key: wrong method arguments", iarg);
        } catch (InvocationTargetException ite) {
            LOGGER.debug("recoder2key: called method " + m + " threw exception ",
                ite.getTargetException());
            if (ite.getTargetException() instanceof ConvertException) {
                throw (ConvertException) ite.getTargetException();
            } else {
                Recoder2KeY.reportError("called method " + m + " threw exception.",
                    ite.getTargetException());
            }
        }

        // set the parental class attribute if available
        if ((currentClassURI != null) && (result instanceof Statement)
                && !(result instanceof SchemaVariable)) {
            ((JavaProgramElement) result).setParentClass(currentClassURI);
        }

        Debug.assertTrue(result instanceof ProgramElement || result == null,
            "the result is not a ProgramElement but", result);

        return result;

    }

    // ==== HELPER FUNCTIONS ===============================================

    /**
     * iterate over all children and call convert upon them. Gather the resulting KeY structures in
     * an ExtList.
     * <p>
     * In addition to the child ast-branches, all comments are gathered also.
     *
     * @param pe the NonTerminalProgramElement that needs its children before being converted
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
            for (recoder.java.Comment comment : l) {
                children.add(convert(comment));
            }
        }

        children.add(positionInfo(pe));
        return children;
    }

    /**
     * replace some numbers from anonymous class names. needed by the translation of anonymous
     * classes.
     */
    static String makeAdmissibleName(String s) {
        return s;
        /*
         * int i = s.indexOf("."); while(i!=-1){ if(s.charAt(i+1)<='9' && s.charAt(i+1)>='0') { s =
         * s.substring(0, i)+"_"+s.substring(i+1); } i = s.indexOf(".", i+1); } return s;
         */
    }


    /**
     * collects comments and adds their converted KeY-counterpart to the list of children
     *
     * @param pe the ProgramElement that needs its comments before being converted
     * @return the list of comments after conversion
     */
    private ExtList collectComments(recoder.java.ProgramElement pe) {
        ExtList children = new ExtList();
        ASTList<recoder.java.Comment> l = pe.getComments();
        if (l != null) {
            for (recoder.java.Comment comment : l) {
                children.add(convert(comment));
            }
        }
        return children;
    }

    /**
     * collects both comments and children of a program element
     *
     * @param pe program element
     * @return freshly created list of children after conversion and converted comments
     */
    private ExtList collectChildrenAndComments(recoder.java.ProgramElement pe) {
        ExtList ret = new ExtList();

        if (pe instanceof recoder.java.NonTerminalProgramElement) {
            ret.addAll(collectChildren((NonTerminalProgramElement) pe));
        }
        ret.addAll(collectComments(pe));

        return ret;
    }

    /**
     * convert recoder position info to key position info
     *
     * @param se the sourcelement to extract from, not null
     * @return the newly created PositionInfo
     */
    private PositionInfo positionInfo(recoder.java.SourceElement se) {
        var relPos = se.getRelativePosition();
        var startPos = Position.fromSEPosition(se.getStartPosition());
        var endPos = Position.fromSEPosition(se.getEndPosition());
        if ((!inLoopInit)) {
            return new PositionInfo(relPos, startPos, endPos, currentClassURI);
        } else {
            return new PositionInfo(relPos, startPos, endPos);
        }
    }

    /**
     * @return a literal constant representing the value of <code>p_er</code>
     */
    private Literal getLiteralFor(recoder.service.ConstantEvaluator.EvaluationResult p_er) {
        return switch (p_er.getTypeCode()) {
            case recoder.service.ConstantEvaluator.BOOLEAN_TYPE -> BooleanLiteral.getBooleanLiteral(p_er.getBoolean());
            case recoder.service.ConstantEvaluator.CHAR_TYPE -> new CharLiteral(p_er.getChar());
            case recoder.service.ConstantEvaluator.DOUBLE_TYPE -> new DoubleLiteral(p_er.getDouble());
            case recoder.service.ConstantEvaluator.FLOAT_TYPE -> new FloatLiteral(p_er.getFloat());
            case recoder.service.ConstantEvaluator.BYTE_TYPE -> new IntLiteral(p_er.getByte());
            case recoder.service.ConstantEvaluator.SHORT_TYPE -> new IntLiteral(p_er.getShort());
            case recoder.service.ConstantEvaluator.INT_TYPE -> new IntLiteral(p_er.getInt());
            case recoder.service.ConstantEvaluator.LONG_TYPE -> new LongLiteral(p_er.getLong());
            case recoder.service.ConstantEvaluator.STRING_TYPE -> {
                if (p_er.getString() == null) {
                    yield NullLiteral.NULL;
                }
                yield new StringLiteral("\"" + p_er.getString() + "\"");
            }
            default -> throw new ConvertException(
                    "Don't know how to handle type " + p_er.getTypeCode() + " of " + p_er);
        };
    }


    /**
     * extracts all fields out of fielddeclaration
     *
     * @param field the FieldDeclaration of which the field specifications have to be extracted
     * @return a IList<Field> the includes all field specifications found int the field declaration
     *         of the given list
     */
    private ImmutableList<Field> filterField(FieldDeclaration field) {
        ImmutableList<Field> result = ImmutableSLList.nil();
        ImmutableArray<FieldSpecification> spec = field.getFieldSpecifications();
        for (int i = spec.size() - 1; i >= 0; i--) {
            result = result.prepend(spec.get(i));
        }
        return result;
    }

    /**
     * retrieves a field with the given name out of the list
     *
     * @param name a String with the name of the field to be looked for
     * @param fields the IList<Field> where we have to look for the field
     * @return the program variable of the given name or null if not found
     */
    private ProgramVariable find(String name, ImmutableList<Field> fields) {
        for (Field field1 : fields) {
            Field field = field1;
            if (name.equals(field.getName())) {
                return (ProgramVariable) ((FieldSpecification) field).getProgramVariable();
            }
        }
        return null;
    }

    // ==== CONVERT METHODS ================================================

    // ----- the standard mechanism

    /**
     * The default procedure.
     * <p>
     * It iterates over all children, calls convert upon them
     * <p>
     * collect all children, convert them. Create a new instance of the corresponding KeY class and
     * call its constructor with the list of children.
     *
     * @param pe the recoder.java.ProgramElement to be converted
     * @return the converted de.uka.ilkd.key.java.JavaProgramElement, null if there has been an
     *         exception
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
        final Class<? extends recoder.java.JavaProgramElement> class_ = pe.getClass();

        try {
            result = (ProgramElement) getKeYClassConstructor(class_).newInstance(parameter);
            return result;
        } catch (Exception e) {
            final String className = class_.toString().substring(6);
            final StringBuilder sb = new StringBuilder(className);
            sb.append('(');
            for (Object p : parameter) {
                sb.append(p.toString());
                sb.append(',');
            }
            if (sb.charAt(sb.length() - 1) == ',') {
                sb.deleteCharAt(sb.length() - 1);
            }
            sb.append(')');
            final String constructorName = sb.toString();
            LOGGER.debug("recoder2key: invocation of constructor {} failed.", constructorName, e);
            Recoder2KeY.reportError("Invocation of the constructor " + constructorName + " failed",
                e);
            throw new Error("unreachable"); // this line is not reachable
            // because reportError fails under
            // any circumstances
        }
    }

    /**
     * gets the KeY-Class related to the recoder one
     *
     * @param recoderClass the original Class within recoder
     * @return the related KeY Class
     * @throws ConvertException for various reasons
     */
    private Class<?> getKeYClass(Class<? extends recoder.java.JavaProgramElement> recoderClass) {
        String className = getKeYName(recoderClass);
        try {
            return Class.forName(className); // Classes are always in this component;
                                             // ClassLoaderUtil#getClassforName(String) does not
                                             // need to be used.
        } catch (ClassNotFoundException cnfe) {
            LOGGER.debug("There is an AST class {} missing at KeY.", className, cnfe);
            throw new ConvertException(
                "Recoder2KeYConverter could not find a conversion from RecodeR "
                    + recoderClass + ".\n"
                    + "Maybe you have added a class to package key.java.recoderext and did not add the equivalent to key.java.expression or its subpackages."
                    + "\nAt least there is no class named " + className + ".",
                cnfe);
        } catch (ExceptionInInitializerError initErr) {
            LOGGER.error("recoder2key: Failed initializing class.", initErr);
            throw new ConvertException("Failed initializing class.", initErr);
        } catch (LinkageError le) {
            LOGGER.error("recoder2key: Linking class failed.", le);
            throw new ConvertException("Linking class failes", le);
        }
    }

    private static final int RECODER_PREFIX_LENGTH = "recoder.".length();

    /**
     * constructs the name of the corresponding KeYClass. Expected prefixes are either recoder or
     * ...key.java.recoderext
     *
     * @param recoderClass Class that is the original recoder
     * @return String containing the KeY-Classname
     */
    private String getKeYName(Class<? extends recoder.java.JavaProgramElement> recoderClass) {
        final String prefix = "de.uka.ilkd.key.";
        final String recoderClassName = recoderClass.getName();
        if (recoderClassName.startsWith("recoder.")) {
            return prefix + recoderClassName.substring(RECODER_PREFIX_LENGTH);
        } else if (recoderClassName.startsWith(prefix + "java.recoderext.")) {
            return recoderClassName.replaceAll("recoderext\\.", "");
        } else {
            assert false : "Unexpected class prefix: " + recoderClassName;
            return "";
        }
    }

    /**
     * determines the right standard constructor of the KeYClass.
     * <p>
     * Use a cache to only look up classes once.
     *
     * @param recoderClass the Class of the recoder AST object
     * @return the Constructor of the right KeY-Class
     */
    private Constructor<?> getKeYClassConstructor(
            Class<? extends recoder.java.JavaProgramElement> recoderClass) {
        Constructor<?> result = null;
        try {
            result = constructorCache.get(recoderClass);

            if (result == null) {
                result = getKeYClass(recoderClass).getConstructor(ExtList.class);
                constructorCache.put(recoderClass, result);
            }
        } catch (NoSuchMethodException nsme) {
            LOGGER.debug("recoder2key: constructor not found. ", nsme);
        } catch (SecurityException se) {
            LOGGER.debug("recoder2key: access denied. ", se);
        }
        return result;
    }

    /**
     * store an element to the recoder {@code <->} key mapping.
     *
     * @param r the recoder element (not null)
     * @param k the key element (not null)
     */
    protected void insertToMap(recoder.ModelElement r, ModelElement k) {

        if (r != null) {
            getMapping().put(r, k);
        } else {
            LOGGER.debug("Tried to store element for null-key - ignored");
        }
    }

    // ------------------- operators ----------------------

    public Instanceof convert(recoder.java.expression.operator.Instanceof rio) {
        return new Instanceof((Expression) callConvert(rio.getExpressionAt(0)),
            (TypeReference) callConvert(rio.getTypeReference()));
    }

    /**
     * converts the recoder.java.expression.operator.NewArray node to the KeYDependance
     */
    public NewArray convert(recoder.java.expression.operator.NewArray newArr) {
        // first we need to collect all children
        ExtList children = collectChildren(newArr);
        // now we have to extract the array initializer
        // is stored separately and must not appear in the children list
        ArrayInitializer arrInit = children.get(ArrayInitializer.class);
        children.remove(arrInit);

        recoder.abstraction.Type javaType =
            getServiceConfiguration().getCrossReferenceSourceInfo().getType(newArr);

        return new NewArray(children, getKeYJavaType(javaType), arrInit, newArr.getDimensions());
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
    public BooleanLiteral convert(recoder.java.expression.literal.BooleanLiteral booleanLit) {

        // The source code position is very important because a single boolean literal is maybe a
        // complete loop condition and the symbolic execution debugger needs source code position to
        // separate code steps from internal proof steps. For this reason is the usage of the
        // singleton constants not possible.
        return booleanLit.getValue()
                ? new BooleanLiteral(collectComments(booleanLit), positionInfo(booleanLit), true)
                : new BooleanLiteral(collectComments(booleanLit), positionInfo(booleanLit), false);
    }


    public EmptySetLiteral convert(de.uka.ilkd.key.java.recoderext.adt.EmptySetLiteral e) {
        return EmptySetLiteral.LOCSET;
    }

    public Singleton convert(de.uka.ilkd.key.java.recoderext.adt.Singleton e) {
        ExtList children = collectChildren(e);
        return new Singleton(children);
    }

    public SetUnion convert(de.uka.ilkd.key.java.recoderext.adt.SetUnion e) {
        ExtList children = collectChildren(e);
        return new SetUnion(children);
    }

    public Intersect convert(de.uka.ilkd.key.java.recoderext.adt.Intersect e) {
        ExtList children = collectChildren(e);
        return new Intersect(children);
    }

    public SetMinus convert(de.uka.ilkd.key.java.recoderext.adt.SetMinus e) {
        ExtList children = collectChildren(e);
        return new SetMinus(children);
    }

    public AllFields convert(de.uka.ilkd.key.java.recoderext.adt.AllFields e) {
        ExtList children = collectChildren(e);
        return new AllFields(children);
    }

    public AllObjects convert(de.uka.ilkd.key.java.recoderext.adt.AllObjects e) {
        ExtList children = collectChildren(e);
        return new AllObjects(children);
    }

    public EmptySeqLiteral convert(de.uka.ilkd.key.java.recoderext.adt.EmptySeqLiteral e) {
        return EmptySeqLiteral.INSTANCE;
    }

    public SeqSingleton convert(de.uka.ilkd.key.java.recoderext.adt.SeqSingleton e) {
        ExtList children = collectChildren(e);
        return new SeqSingleton(children);
    }

    public SeqConcat convert(de.uka.ilkd.key.java.recoderext.adt.SeqConcat e) {
        ExtList children = collectChildren(e);
        return new SeqConcat(children);
    }

    public SeqSub convert(de.uka.ilkd.key.java.recoderext.adt.SeqSub e) {
        ExtList children = collectChildren(e);
        return new SeqSub(children);
    }

    public SeqLength convert(de.uka.ilkd.key.java.recoderext.adt.SeqLength e) {
        return new SeqLength(collectChildren(e));
    }

    public SeqIndexOf convert(de.uka.ilkd.key.java.recoderext.adt.SeqIndexOf e) {
        return new SeqIndexOf(collectChildren(e));
    }

    public SeqReverse convert(de.uka.ilkd.key.java.recoderext.adt.SeqReverse e) {
        ExtList children = collectChildren(e);
        return new SeqReverse(children);
    }

    public SeqPut convert(de.uka.ilkd.key.java.recoderext.adt.SeqPut e) {
        ExtList children = collectChildren(e);
        return new SeqPut(children);
    }

    public EmptyMapLiteral convert(de.uka.ilkd.key.java.recoderext.adt.EmptyMapLiteral e) {
        return EmptyMapLiteral.INSTANCE;
    }

    /**
     * Resolve the function symbol which is embedded here to its logical counterpart.
     */
    public DLEmbeddedExpression convert(de.uka.ilkd.key.java.recoderext.EscapeExpression e) {
        final var PREFIX = "\\dl_DEFAULT_VALUE_";
        final var DEFVALUE = "@defaultValue(";
        ExtList children = collectChildren(e);
        String name = e.getFunctionName();

        if (name.startsWith(PREFIX)) { // handle default value resolution
            String sortName = name.substring(PREFIX.length()).trim();
            Sort sort = namespaceSet.sorts().lookup(sortName);
            if (sort == null) {
                throw new ConvertException(format(
                    "Requested to find the default value of an unknown sort '%s'. " + "Line/Col:%s",
                    sortName, e.getStartPosition()));
            }

            var doc = sort.getDocumentation();

            if (doc == null) {
                throw new ConvertException(
                    format("Requested to find the default value for the sort '%s', "
                        + "which does not have a documentary comment. The sort is defined at %s. "
                        + "Line/Col: %s", sortName, sort.getOrigin(), e.getStartPosition()));
            }

            int pos = doc.indexOf(DEFVALUE);
            if (pos >= 0) {
                int start = doc.indexOf('(', pos) + 1;
                int closing = doc.indexOf(')', pos);

                if (closing < 0) {
                    throw new ConvertException(format(
                        "Forgotten closing parenthesis on @defaultValue annotation for sort '%s' in '%s'",
                        sortName, sort.getOrigin()));
                }

                // set this as the function name, as the user had written \dl_XXX
                name = doc.substring(start, closing);
            } else {
                throw new ConvertException(format(
                    "Could not infer the default value for the given sort '%s'. "
                        + "The sort found was as '%s' and the sort's documentation is '%s'. "
                        + "Did you forget @defaultValue(XXX) in the documentation?Line/Col: %s",
                    sortName, sort, doc, e.getStartPosition()));
            }
        }


        JFunction named = namespaceSet.functions().lookup(new Name(name));

        if (named == null) {
            // TODO provide position information?!
            throw new ConvertException(format(
                "In an embedded DL expression, %s is not a known DL function name. Line/Col:%s",
                name, e.getStartPosition()));
        }

        DLEmbeddedExpression expression = new DLEmbeddedExpression(named, children);
        expression.check(services, getKeYJavaType(
            getServiceConfiguration().getCrossReferenceSourceInfo().getContainingClassType(e)));
        return expression;
    }

    public SeqGet convert(de.uka.ilkd.key.java.recoderext.adt.SeqGet e) {
        return new SeqGet(collectChildren(e));
    }

    /** convert a recoder StringLiteral to a KeY StringLiteral */
    public StringLiteral convert(recoder.java.expression.literal.StringLiteral stringLit) {
        return new StringLiteral(collectComments(stringLit), stringLit.getValue());
    }

    /** convert a recoder DoubleLiteral to a KeY DoubleLiteral */
    public DoubleLiteral convert(recoder.java.expression.literal.DoubleLiteral doubleLit) {
        return new DoubleLiteral(collectComments(doubleLit), doubleLit.getValue());
    }

    /** convert a recoder FloatLiteral to a KeY FloatLiteral */
    public FloatLiteral convert(recoder.java.expression.literal.FloatLiteral floatLit) {

        return new FloatLiteral(collectComments(floatLit), floatLit.getValue());
    }

    /**
     * convert a recoder LongLiteral to a KeY LongLiteral
     *
     * @param longLit the LongLiteral from recoder
     * @return a KeY LongLiteral (immutable)
     */
    public LongLiteral convert(recoder.java.expression.literal.LongLiteral longLit) {
        return new LongLiteral(collectComments(longLit), longLit.getValue());
    }

    /**
     * convert a recoder CharLiteral to a KeY CharLiteral
     *
     * @param charLit the CharLiteral from recoder
     * @return a KeY CharLiteral (immutable)
     */
    public CharLiteral convert(recoder.java.expression.literal.CharLiteral charLit) {
        return new CharLiteral(collectComments(charLit), charLit.getValue());
    }

    /** convert a recoder NullLiteral to a KeY NullLiteral */
    public NullLiteral convert(recoder.java.expression.literal.NullLiteral nullLit) {

        recoder.abstraction.Type javaType =
            getServiceConfiguration().getCrossReferenceSourceInfo().getType(nullLit);
        getKeYJavaType(javaType);

        // if there are comments to take into consideration
        // change parameter to ExtList
        // TODO make comments available
        return NullLiteral.NULL;
    }

    // ----------------------------------------------------------

    /** convert a recoder Identifier to a KeY Identifier */
    public ProgramElementName convert(recoder.java.Identifier id) {
        final NonTerminalProgramElement parent = id.getParent();
        if (parent instanceof recoder.java.reference.VariableReference ||
                parent instanceof recoder.java.declaration.VariableSpecification) {
            return VariableNamer.parseName(id.getText(),
                collectComments(id).collect(Comment.class));
        } else {
            return new ProgramElementName(id.getText(), collectComments(id).collect(Comment.class));
        }
    }

    public ProgramElementName convert(ImplicitIdentifier id) {
        return new ProgramElementName(id.getText(), collectComments(id).collect(Comment.class));
    }

    /** convert a recoderext MethodFrameStatement to a KeY MethodFrameStatement */
    public MethodFrame convert(de.uka.ilkd.key.java.recoderext.MethodCallStatement rmcs) {
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
        } else {
            throw new ConvertException("Methodframe statement has no body " + rmcs);
        }

        return new MethodFrame(resVar, convert(rmcs.getExecutionContext()), block);
    }

    /** convert a recoderext MethodBodyStatement to a KeY MethodBodyStatement */
    public MethodBodyStatement convert(de.uka.ilkd.key.java.recoderext.MethodBodyStatement rmbs) {

        final TypeReference bodySource = convert(rmbs.getBodySource());
        final IProgramVariable resultVar = rmbs.getResultVariable() != null
                ? (IProgramVariable) callConvert(rmbs.getResultVariable())
                : null;
        final ReferencePrefix invocationTarget =
            (ReferencePrefix) callConvert(rmbs.getReferencePrefix());
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

        final MethodReference mr = new MethodReference(new ImmutableArray<>(keyArgs),
            methodName, invocationTarget);

        return new MethodBodyStatement(bodySource, resultVar, mr);
    }

    public LoopScopeBlock convert(de.uka.ilkd.key.java.recoderext.LoopScopeBlock lsb) {
        return new LoopScopeBlock((IProgramVariable) callConvert(lsb.getIndexPV()),
            (StatementBlock) callConvert(lsb.getBody()));
    }

    public MergePointStatement convert(de.uka.ilkd.key.java.recoderext.MergePointStatement mps) {
        final LocationVariable locVar =
            new LocationVariable(services.getVariableNamer().getTemporaryNameProposal("x"),
                services.getNamespaces().sorts().lookup("boolean"));

        final Comment[] comments = new Comment[mps.getComments().size()];
        for (int i = 0; i < mps.getComments().size(); i++) {
            comments[i] = convert(mps.getComments().get(i));
        }

        return new MergePointStatement(locVar, comments);
    }

    public CatchAllStatement convert(de.uka.ilkd.key.java.recoderext.CatchAllStatement cas) {
        return new CatchAllStatement((StatementBlock) callConvert(cas.getStatementAt(0)),
            (LocationVariable) callConvert(cas.getVariable()));
    }

    /**
     * convert a recorder JML assert statment into a KeY JML assert statement.
     *
     * @param ja the statement to convert
     * @return the converted statement
     */
    public JmlAssert convert(de.uka.ilkd.key.java.recoderext.JmlAssert ja) {
        return new JmlAssert(ja.getKind(), ja.getCondition(), positionInfo(ja));
    }

    // ------------------- declaration ---------------------

    /** convert a recoder ClassDeclaration to a KeY ClassDeclaration */
    public ClassDeclaration convert(recoder.java.declaration.ClassDeclaration td) {

        KeYJavaType kjt = getKeYJavaType(td);
        ExtList classMembers = collectChildren(td);

        ClassDeclaration keYClassDecl = new ClassDeclaration(classMembers,
            new ProgramElementName(makeAdmissibleName(td.getFullName())), isParsingLibs(),
            td.getContainingClassType() != null, td.getName() == null,
            td.getStatementContainer() != null);
        // new ProgramElementName(td.getFullName()), isParsingLibs());

        kjt.setJavaType(keYClassDecl);
        return keYClassDecl;
    }

    /**
     * convert a recoder EnumDeclaration to a KeY EnumClassDeclaration. Enums have already been
     * mapped to classes at an earlier stage
     *
     * @author m.u.
     */
    public EnumClassDeclaration convert(de.uka.ilkd.key.java.recoderext.EnumClassDeclaration td) {

        KeYJavaType kjt = getKeYJavaType(td);
        ExtList classMembers = collectChildren(td);

        EnumClassDeclaration keyEnumDecl =
            new EnumClassDeclaration(classMembers, new ProgramElementName(td.getFullName()),
                isParsingLibs(), td.getEnumConstantDeclarations());

        kjt.setJavaType(keyEnumDecl);
        return keyEnumDecl;
    }

    public InterfaceDeclaration convert(recoder.java.declaration.InterfaceDeclaration td) {

        KeYJavaType kjt = getKeYJavaType(td);
        ExtList members = collectChildren(td);
        InterfaceDeclaration keYInterfaceDecl = new InterfaceDeclaration(members,
            new ProgramElementName(td.getFullName()), isParsingLibs());
        kjt.setJavaType(keYInterfaceDecl);

        return keYInterfaceDecl;
    }

    /**
     * converts a recoder ParameterDeclaration to a KeY ParameterDeclaration (especially the
     * declaration type of its parent is determined and handed over)
     */
    public ParameterDeclaration convert(recoder.java.declaration.ParameterDeclaration pd) {
        return new ParameterDeclaration(collectChildren(pd),
            pd.getASTParent() instanceof recoder.java.declaration.InterfaceDeclaration,
            pd.isVarArg());
    }

    /**
     * convert a recoder FieldDeclaration to a KeY FieldDeclaration (especially the declaration type
     * of its parent is determined and handed over)
     */
    public FieldDeclaration convert(recoder.java.declaration.FieldDeclaration fd) {
        return new FieldDeclaration(collectChildren(fd),
            fd.getASTParent() instanceof recoder.java.declaration.InterfaceDeclaration);
    }

    /**
     * convert a recoder ConstructorDeclaration to a KeY IProgramMethod (especially the declaration
     * type of its parent is determined and handed over)
     */
    public IProgramMethod convert(recoder.java.declaration.ConstructorDeclaration cd) {
        ConstructorDeclaration consDecl = new ConstructorDeclaration(collectChildren(cd),
            cd.getASTParent() instanceof recoder.java.declaration.InterfaceDeclaration);
        recoder.abstraction.ClassType cont = getServiceConfiguration().getCrossReferenceSourceInfo()
                .getContainingClassType((recoder.abstraction.Member) cd);

        final HeapLDT heapLDT = rec2key.getTypeConverter().getTypeConverter().getHeapLDT();
        Sort heapSort = heapLDT == null ? JavaDLTheory.ANY : heapLDT.targetSort();
        final KeYJavaType containerKJT = getKeYJavaType(cont);
        IProgramMethod result = new ProgramMethod(consDecl, containerKJT, KeYJavaType.VOID_TYPE,
            positionInfo(cd), heapSort, heapLDT == null ? 1 : heapLDT.getAllHeaps().size() - 1);
        insertToMap(cd, result);
        return result;
    }

    /**
     * convert a recoder DefaultConstructor to a KeY IProgramMethod (especially the declaration type
     * of its parent is determined and handed over)
     */
    public IProgramMethod convert(recoder.abstraction.DefaultConstructor dc) {
        ExtList children = new ExtList();
        children.add(new ProgramElementName(dc.getName()));
        ConstructorDeclaration consDecl =
            new ConstructorDeclaration(children, dc.getContainingClassType().isInterface());
        recoder.abstraction.ClassType cont = dc.getContainingClassType();
        final HeapLDT heapLDT = rec2key.getTypeConverter().getTypeConverter().getHeapLDT();
        Sort heapSort = heapLDT == null ? JavaDLTheory.ANY : heapLDT.targetSort();
        final KeYJavaType containerKJT = getKeYJavaType(cont);
        IProgramMethod result =
            new ProgramMethod(consDecl, containerKJT, KeYJavaType.VOID_TYPE, PositionInfo.UNDEFINED,
                heapSort, heapLDT == null ? 1 : heapLDT.getAllHeaps().size() - 1);
        insertToMap(dc, result);
        return result;
    }

    /** convert a recoder type cast to a KeY TypeCast */
    public TypeCast convert(recoder.java.expression.operator.TypeCast c) {
        return new TypeCast((Expression) callConvert(c.getExpressionAt(0)),
            (TypeReference) callConvert(c.getTypeReference()));
    }

    /**
     * converts a SpecialConstructorReference. Special handling because the initializing Expressions
     * and the ReferencePrefix accessPath might not be disjunct.
     */
    public SuperConstructorReference convert(recoder.java.reference.SuperConstructorReference scr) {

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
     * Convert a this referene. Special handling because the initializing Expressions and the
     * ReferencePrefix accessPath might not be disjunct.
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
     * Convert a super referene. Special handling because the initializing Expressions and the
     * ReferencePrefix accessPath might not be disjunct.
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
     * convert a recoder VariableSpecification to a KeY VariableSpecification (checks dimension and
     * hands it over and insert in hashmap)
     */
    public VariableSpecification convert(
            recoder.java.declaration.VariableSpecification recoderVarSpec) {

        VariableSpecification varSpec = (VariableSpecification) getMapping().toKeY(recoderVarSpec);

        if (varSpec == null) {
            recoder.abstraction.Type recoderType =
                (getServiceConfiguration().getSourceInfo()).getType(recoderVarSpec);

            final ProgramElementName name =
                VariableNamer.parseName(makeAdmissibleName(recoderVarSpec.getName()));
            var isGhost = containsModifier(recoderVarSpec.getParent(),
                de.uka.ilkd.key.java.recoderext.Ghost.class);
            var isFinal = recoderVarSpec.isFinal();

            final ProgramVariable pv =
                new LocationVariable(name, getKeYJavaType(recoderType), isGhost, isFinal);
            varSpec = new VariableSpecification(collectChildren(recoderVarSpec), pv,
                recoderVarSpec.getDimensions(), pv.getKeYJavaType());

            insertToMap(recoderVarSpec, varSpec);
        }
        return varSpec;
    }

    /**
     * convert a recoder MethodDeclaration to a KeY IProgramMethod (especially the declaration type
     * of its parent is determined and handed over)
     */
    public IProgramMethod convert(recoder.java.declaration.MethodDeclaration md) {
        IProgramMethod result = null;

        // methodsDeclaring contains the recoder method declarations as keys
        // that have been started to convert but are not yet finished.
        // The mapped value is the reference to the later completed
        // IProgramMethod.
        if (methodsDeclaring.containsKey(md)) {
            // a recursive call from a method reference
            return methodsDeclaring.get(md);
            // reference that will later be set.
        }

        methodsDeclaring.put(md, result);
        if (!getMapping().mapped(md)) {

            // If the method is 'void', the 'void' type reference
            // gets lost in translation: the KeY AST uses "null" instead of
            // it. However, the type reference may have attached JML comments
            // (in particular, with the "helper" keyword) that we must keep.
            Comment[] voidComments = null;
            if (md.getTypeReference() != null && md.getTypeReference().getName().equals("void")) {
                final ASTList<recoder.java.Comment> trComs = md.getTypeReference().getComments();
                if (trComs != null) {
                    voidComments = new Comment[trComs.size()];
                    for (int i = 0; i < voidComments.length; i++) {
                        voidComments[i] = convert(trComs.get(i));
                    }
                }
            }

            final MethodDeclaration methDecl = new MethodDeclaration(collectChildren(md),
                md.getASTParent() instanceof recoder.java.declaration.InterfaceDeclaration,
                voidComments);
            recoder.abstraction.ClassType cont =
                getServiceConfiguration().getCrossReferenceSourceInfo()
                        .getContainingClassType((recoder.abstraction.Member) md);

            final HeapLDT heapLDT = rec2key.getTypeConverter().getTypeConverter().getHeapLDT();
            Sort heapSort = heapLDT == null ? JavaDLTheory.ANY : heapLDT.targetSort();
            final KeYJavaType containerType = getKeYJavaType(cont);
            assert containerType != null;
            final Type returnType = md.getReturnType();
            // may be null for a void method
            final KeYJavaType returnKJT =
                returnType == null ? KeYJavaType.VOID_TYPE : getKeYJavaType(returnType);
            result = new ProgramMethod(methDecl, containerType, returnKJT, positionInfo(md),
                heapSort, heapLDT == null ? 1 : heapLDT.getAllHeaps().size() - 1);

            insertToMap(md, result);
        }
        methodsDeclaring.remove(md);
        result = (IProgramMethod) getMapping().toKeY(md);
        return result;
    }

    /**
     * convert a recoder FieldSpecification to a KeY FieldSpecification (checks dimension and hands
     * it over and insert in hash map)
     */
    public FieldSpecification convert(recoder.java.declaration.FieldSpecification recoderVarSpec) {

        if (recoderVarSpec == null) { // %%%%%%%%%%%%%
            return new FieldSpecification();
        }

        FieldSpecification varSpec = (FieldSpecification) getMapping().toKeY(recoderVarSpec);

        if (varSpec == null) {
            recoder.abstraction.Type recoderType =
                (getServiceConfiguration().getSourceInfo()).getType(recoderVarSpec);

            ProgramVariable pv = getProgramVariableForFieldSpecification(recoderVarSpec);

            if (recoderVarSpec.getIdentifier() instanceof ImplicitIdentifier) {
                // the modelled field is an implicit one, we have to handle this
                // one
                // explicit
                varSpec = new ImplicitFieldSpecification(pv, getKeYJavaType(recoderType));
            } else {
                varSpec = new FieldSpecification(collectChildren(recoderVarSpec), pv,
                    recoderVarSpec.getDimensions(), getKeYJavaType(recoderType));
            }
            insertToMap(recoderVarSpec, varSpec);
        }

        return varSpec;
    }

    private static boolean containsModifier(recoder.java.declaration.JavaDeclaration fs,
            Class<? extends DeclarationSpecifier> cls) {
        ASTList<DeclarationSpecifier> specifiers = fs.getDeclarationSpecifiers();
        int s = (specifiers == null) ? 0 : specifiers.size();
        for (int i = 0; i < s; i += 1) {
            if (cls.isInstance(specifiers.get(i))) {
                return true;
            }
        }
        return false;
    }

    /**
     * this is needed by #convert(FieldSpecification).
     */
    private ProgramVariable getProgramVariableForFieldSpecification(
            recoder.java.declaration.FieldSpecification recoderVarSpec) {

        if (recoderVarSpec == null) {
            return null;
        }

        ProgramVariable pv = fieldSpecificationMapping.get(recoderVarSpec);

        if (pv == null) {
            VariableSpecification varSpec =
                (VariableSpecification) getMapping().toKeY(recoderVarSpec);
            if (varSpec == null) {
                recoder.abstraction.Type recoderType =
                    (getServiceConfiguration().getSourceInfo()).getType(recoderVarSpec);
                final ClassType recContainingClassType = recoderVarSpec.getContainingClassType();
                final ProgramElementName pen =
                    new ProgramElementName(makeAdmissibleName(recoderVarSpec.getName()),
                        makeAdmissibleName(recContainingClassType.getFullName()));

                final Literal compileTimeConstant =
                    getCompileTimeConstantInitializer(recoderVarSpec);

                boolean isModel = containsModifier(recoderVarSpec.getParent(),
                    de.uka.ilkd.key.java.recoderext.Model.class);
                boolean isFinal = recoderVarSpec.isFinal();
                boolean isGhost = containsModifier(recoderVarSpec.getParent(),
                    de.uka.ilkd.key.java.recoderext.Ghost.class);

                if (compileTimeConstant == null) {
                    pv = new LocationVariable(pen, getKeYJavaType(recoderType),
                        getKeYJavaType(recContainingClassType), recoderVarSpec.isStatic(), isModel,
                        isGhost, isFinal);
                } else {
                    pv = new ProgramConstant(pen, getKeYJavaType(recoderType),
                        getKeYJavaType(recContainingClassType), recoderVarSpec.isStatic(),
                        compileTimeConstant);
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
     *         <code>recoderVarSpec</code>, if the variable is a compile-time constant, and
     *         <code>null</code> otherwise
     */
    private Literal getCompileTimeConstantInitializer(
            recoder.java.declaration.FieldSpecification recoderVarSpec) {

        // Necessary condition: the field is static and final
        if (!recoderVarSpec.isFinal() || !recoderVarSpec.isStatic()) {
            return null;
        }

        recoder.java.Expression init = recoderVarSpec.getInitializer();

        if (init != null) {
            recoder.service.ConstantEvaluator ce =
                new recoder.service.DefaultConstantEvaluator(getServiceConfiguration());
            recoder.service.ConstantEvaluator.EvaluationResult er =
                new recoder.service.ConstantEvaluator.EvaluationResult();

            try {
                if (ce.isCompileTimeConstant(init, er)) {
                    return getLiteralFor(er);
                }
            } catch (NumberFormatException | ArithmeticException t) {
            }
        }

        return null;
    }

    /**
     * convert a recoder TypeReference to a KeY TypeReference (checks dimension and hands it over)
     */
    public TypeReference convert(recoder.java.reference.TypeReference tr) {

        recoder.abstraction.Type rType = getServiceConfiguration().getSourceInfo().getType(tr);

        if (rType == null) {
            return null; // because of 'void'
        }

        KeYJavaType kjt = getKeYJavaType(rType);
        ExtList children = collectChildren(tr);
        TypeReference result = new TypeRef(children, kjt, tr.getDimensions());
        return result;
    }

    /**
     * if an UncollatedReferenceQualifier appears throw a ConvertExceception because these
     * qualifiers have to be resolved by running the CrossReferencer
     */
    public ProgramElement convert(recoder.java.reference.UncollatedReferenceQualifier urq) {
        recoder.java.ProgramElement pe =
            getServiceConfiguration().getCrossReferenceSourceInfo().resolveURQ(urq);
        if (pe != null && !(pe instanceof recoder.java.reference.UncollatedReferenceQualifier)) {
            return (ProgramElement) callConvert(pe);
        }
        throw new PosConvertException(
            "recoder2key: Qualifier " + urq.getName() + " not resolvable.",
            Position.fromSEPosition(urq.getFirstElement().getStartPosition()));
    }

    /**
     * this is needed to convert variable references
     */
    private recoder.java.declaration.VariableSpecification getRecoderVarSpec(
            recoder.java.reference.VariableReference vr) {
        return getServiceConfiguration().getSourceInfo().getVariableSpecification(
            getServiceConfiguration().getSourceInfo().getVariable(vr));
    }

    /**
     * converts a recoder variable reference. A ProgramVariable is created replacing the variable
     * reference.
     *
     * @param vr the recoder variable reference.
     */
    public ProgramVariable convert(recoder.java.reference.VariableReference vr) {

        final recoder.java.declaration.VariableSpecification recoderVarspec = getRecoderVarSpec(vr);

        if (!getMapping().mapped(recoderVarspec)) {
            insertToMap(recoderVarspec, convert(recoderVarspec));
        }

        return (ProgramVariable) ((VariableSpecification) getMapping().toKeY(recoderVarspec))
                .getProgramVariable();
    }

    /**
     * converts a recoder array length reference to a usual KeY field reference
     */
    public FieldReference convert(recoder.java.reference.ArrayLengthReference alr) {
        recoder.abstraction.Type recoderType = getServiceConfiguration()
                .getCrossReferenceSourceInfo().getType(alr.getReferencePrefix());
        ArrayDeclaration ad = (ArrayDeclaration) getKeYJavaType(recoderType).getJavaType();

        final ProgramVariable length = find("length", filterField(ad.length()));
        // the invocation of callConvert should work well as each array
        // length reference must have a reference prefix (at least this
        // is what i think)
        return new FieldReference(length, (ReferencePrefix) callConvert(alr.getReferencePrefix()));
    }

    /**
     * converts a recoder field reference. A ProgramVariable is created replacing the field
     * reference.
     *
     * @param fr the recoder field reference.
     */
    public Expression convert(recoder.java.reference.FieldReference fr) {
        ProgramVariable pv;

        recoder.java.declaration.FieldSpecification recoderVarSpec =
            (recoder.java.declaration.FieldSpecification) getRecoderVarSpec(fr);

        ReferencePrefix prefix = null;

        if (fr.getReferencePrefix() != null) {
            prefix = (ReferencePrefix) callConvert(fr.getReferencePrefix());
        }

        if (recoderVarSpec == null) {
            // null means only bytecode available for this field %%%
            recoder.abstraction.Field recField =
                getServiceConfiguration().getSourceInfo().getField(fr);
            recoder.abstraction.Type recoderType =
                getServiceConfiguration().getByteCodeInfo().getType(recField);
            recoder.java.declaration.FieldSpecification fs =
                new recoder.java.declaration.FieldSpecification(fr.getIdentifier());

            final boolean isModel = false; // bytecode-only fields are no model fields
            final boolean isFinal = fs.isFinal();

            pv = new LocationVariable(
                new ProgramElementName(makeAdmissibleName(fs.getName()),
                    makeAdmissibleName(recField.getContainingClassType().getFullName())),
                getKeYJavaType(recoderType), getKeYJavaType(recField.getContainingClassType()),
                recField.isStatic(), isModel, false, isFinal);
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
     * converts a recoder method reference. A de.uka.ilkd.key.logic.op.ProgramMethod is created
     * replacing the method reference.
     *
     * @param mr the recoder method reference.
     * @return the Method the KeY Dependance
     */
    public MethodReference convert(recoder.java.reference.MethodReference mr) {
        recoder.service.SourceInfo sourceInfo = getServiceConfiguration().getSourceInfo();
        recoder.abstraction.Method method = sourceInfo.getMethod(mr);

        final IProgramMethod pm;
        if (!getMapping().mapped(method)) {
            if (method instanceof recoder.java.declaration.MethodDeclaration) {
                // method reference before method decl, also recursive calls.
                // do not use:
                final URI oldCurrent = currentClassURI;

                recoder.io.DataLocation loc = null;
                TypeDeclaration td =
                    ((recoder.java.declaration.MethodDeclaration) method).getMemberParent();
                NonTerminalProgramElement tdc = td.getParent();
                while (tdc != null && !(tdc instanceof recoder.java.CompilationUnit)) {
                    tdc = tdc.getASTParent();
                }
                loc = tdc instanceof recoder.java.CompilationUnit
                        ? ((recoder.java.CompilationUnit) tdc).getOriginalDataLocation()
                        : null;

                currentClassURI = MiscTools.extractURI(loc).orElse(null);
                pm = convert((recoder.java.declaration.MethodDeclaration) method);
                // because of cycles when reading recursive programs
                currentClassURI = oldCurrent;
            } else {
                // bytecode currently we do nothing
                pm = null;
            }
        } else {
            pm = (IProgramMethod) getMapping().toKeY(method);
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
            pm == null ? new ProgramElementName(mr.getName()) : pm.getProgramElementName(), prefix,
            positionInfo(mr), null);
    }

    // --------------Special treatment because of ambiguities ----------

    /**
     * convert a labeled statement. Remove the label from the set of children and pass it
     * separately.
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
     * @param f the For of recoder
     * @return the For of KeY
     */
    public For convert(recoder.java.statement.For f) {
        return new For(convertLoopInitializers(f), convertGuard(f), convertUpdates(f),
            convertBody(f), collectComments(f), positionInfo(f));
    }

    public AnnotationUseSpecification convert(
            recoder.java.declaration.AnnotationUseSpecification aus) {
        return new AnnotationUseSpecification((TypeReference) callConvert(aus.getTypeReference()));
    }

    /**
     * converts a java5-enhanced-for.
     *
     * @param f the EnhancedFor of recoder
     * @return the EnhancedFor of KeY
     */

    public EnhancedFor convert(recoder.java.statement.EnhancedFor f) {
        return new EnhancedFor(convertLoopInitializers(f), convertGuard(f), convertBody(f),
            collectComments(f), positionInfo(f));
    }

    /**
     * converts a While.
     *
     * @param w the While of recoder
     * @return the While of KeY
     */
    public While convert(recoder.java.statement.While w) {
        return new While(convertGuard(w).getExpression(), convertBody(w), positionInfo(w),
            collectComments(w));
    }

    /**
     * converts a Do.
     *
     * @param d the Do of recoder
     * @return the Do of KeY
     */
    public Do convert(recoder.java.statement.Do d) {
        return new Do(convertGuard(d).getExpression(), convertBody(d), collectComments(d),
            positionInfo(d));
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
            for (recoder.java.Expression recLoopUpdate : recLoopUpdates) {
                updates.add(callConvert(recLoopUpdate));
            }
            inLoopInit = false;
            return new ForUpdates(updates, positionInfo(ls));
        }
        return null;
    }

    /**
     * helper for convert(x) with x a LoopStatement. Converts the loop initializers of x.
     */
    public LoopInit convertLoopInitializers(recoder.java.statement.LoopStatement ls) {

        final LoopInit loopInit;

        ASTList<recoder.java.LoopInitializer> initializers = ls.getInitializers();
        if (initializers != null) {
            final LoopInitializer[] result = new LoopInitializer[initializers.size()];
            for (int i = 0, sz = initializers.size(); i < sz; i++) {
                inLoopInit = true;
                result[i] = (LoopInitializer) callConvert(initializers.get(i));
                inLoopInit = false;
            }
            loopInit = new LoopInit(result);
        } else {
            loopInit = null;
        }
        return loopInit;
    }

    /**
     * converts an ArrayReference. Special handling because the initializing Expressions and the
     * ReferencePrefix accessPath might not be disjunct.
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
        return new Assert((Expression) callConvert(a.getCondition()), message, positionInfo(a));
    }

    /**
     * converts a Case. Special handling because the initializing Expression and Statements might
     * not be disjunct.
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
     * converts a New. Special handling because the ReferencePrefix and the TypeReference might not
     * be disjunct.
     */
    public New convert(recoder.java.expression.operator.New n) {

        ASTList<recoder.java.Expression> args = n.getArguments();
        final recoder.java.reference.ReferencePrefix rp = n.getReferencePrefix();
        recoder.service.CrossReferenceSourceInfo si =
            getServiceConfiguration().getCrossReferenceSourceInfo();
        final recoder.java.reference.TypeReference tr = n.getTypeReference();
        final recoder.java.declaration.ClassDeclaration cd = n.getClassDeclaration();

        LinkedList<?> outerVars = null;
        if (locClass2finalVar != null) {
            outerVars = (LinkedList<?>) locClass2finalVar.get(cd);
        }

        int numVars = outerVars != null ? outerVars.size() : 0;

        final Expression[] arguments;

        if (args != null) {
            arguments = new Expression[args.size() + numVars];
            for (int i = 0; i < arguments.length - numVars; i++) {
                arguments[i] = (Expression) callConvert(args.get(i));
            }
        } else {
            arguments = new Expression[numVars];
        }

        if (outerVars != null) {
            for (int i = arguments.length - numVars; i < arguments.length; i++) {
                recoder.java.declaration.VariableSpecification v =
                    (recoder.java.declaration.VariableSpecification) outerVars
                            .get(i - arguments.length + numVars);
                if (si.getContainingClassType(v) != si.getContainingClassType(n)) {
                    recoder.java.declaration.FieldSpecification fs =
                        (recoder.java.declaration.FieldSpecification) si.getVariable(
                            ImplicitFieldAdder.FINAL_VAR_PREFIX + v.getName(),
                            (recoder.java.declaration.ClassDeclaration) si
                                    .getContainingClassType(n));
                    arguments[i] = new FieldReference(getProgramVariableForFieldSpecification(fs),
                        new ThisReference());
                } else {
                    arguments[i] = (ProgramVariable) convert(v).getProgramVariable();
                }
            }
        }

        TypeReference maybeAnonClass = (TypeReference) callConvert(tr);
        if (n.getClassDeclaration() != null) {
            callConvert(n.getClassDeclaration());
            KeYJavaType kjt = getKeYJavaType(n.getClassDeclaration());
            maybeAnonClass = new TypeRef(kjt);
        }

        if (rp == null) {
            return new New(arguments, maybeAnonClass, null);
        } else {
            return new New(arguments, maybeAnonClass, (ReferencePrefix) callConvert(rp));
        }
    }

    public Import convert(recoder.java.Import im) {
        return new Import(collectChildren(im), im.isMultiImport());
    }

    /**
     * convert a statement block and remove all included anonymous classes.
     *
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

    public SetStatement convert(
            de.uka.ilkd.key.java.recoderext.SetStatement arg) {
        return new SetStatement(arg.getParserContext(), positionInfo(arg));
    }

    public TransactionStatement convert(de.uka.ilkd.key.java.recoderext.TransactionStatement tr) {
        return new TransactionStatement(tr.getType());
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
        return new ArrayInitializer(collectChildrenAndComments(arg),
            getKeYJavaType(getServiceConfiguration().getSourceInfo().getType(arg.getASTParent())));
    }

    public Throw convert(recoder.java.statement.Throw arg) {
        return new Throw(collectChildrenAndComments(arg));
    }

    public If convert(recoder.java.statement.If arg) {
        return new If(collectChildrenAndComments(arg));
    }

    public Then convert(recoder.java.statement.Then arg) {
        return new Then(collectChildrenAndComments(arg));
    }

    public Else convert(recoder.java.statement.Else arg) {
        return new Else(collectChildrenAndComments(arg));
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

    public Exec convert(de.uka.ilkd.key.java.recoderext.Exec arg) {
        return new Exec(collectChildrenAndComments(arg));
    }

    public Ccatch convert(de.uka.ilkd.key.java.recoderext.Ccatch arg) {
        return new Ccatch(collectChildrenAndComments(arg));
    }

    public CcatchReturnParameterDeclaration convert(
            de.uka.ilkd.key.java.recoderext.CcatchReturnParameterDeclaration arg) {
        return new CcatchReturnParameterDeclaration(collectChildrenAndComments(arg));
    }

    public CcatchBreakParameterDeclaration convert(
            de.uka.ilkd.key.java.recoderext.CcatchBreakParameterDeclaration arg) {
        return new CcatchBreakParameterDeclaration(collectChildrenAndComments(arg));
    }

    public CcatchBreakWildcardParameterDeclaration convert(
            de.uka.ilkd.key.java.recoderext.CcatchBreakWildcardParameterDeclaration arg) {
        return new CcatchBreakWildcardParameterDeclaration(collectChildrenAndComments(arg));
    }

    public CcatchBreakLabelParameterDeclaration convert(
            de.uka.ilkd.key.java.recoderext.CcatchBreakLabelParameterDeclaration arg) {
        return new CcatchBreakLabelParameterDeclaration(collectChildrenAndComments(arg));
    }

    public CcatchContinueParameterDeclaration convert(
            de.uka.ilkd.key.java.recoderext.CcatchContinueParameterDeclaration arg) {
        return new CcatchContinueParameterDeclaration(collectChildrenAndComments(arg));
    }

    public CcatchContinueWildcardParameterDeclaration convert(
            de.uka.ilkd.key.java.recoderext.CcatchContinueWildcardParameterDeclaration arg) {
        return new CcatchContinueWildcardParameterDeclaration(collectChildrenAndComments(arg));
    }

    public CcatchContinueLabelParameterDeclaration convert(
            de.uka.ilkd.key.java.recoderext.CcatchContinueLabelParameterDeclaration arg) {
        return new CcatchContinueLabelParameterDeclaration(collectChildrenAndComments(arg));
    }

    public CcatchReturnValParameterDeclaration convert(
            de.uka.ilkd.key.java.recoderext.CcatchReturnValParameterDeclaration arg) {
        return new CcatchReturnValParameterDeclaration(collectChildrenAndComments(arg));
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
        TypeReference classContext = convert(arg.getTypeReference());

        IProgramMethod methodContext = null;
        if (arg.getMethodContext() != null) {
            JavaInfo jInfo = services.getJavaInfo();

            ImmutableList<KeYJavaType> paramTypes = ImmutableSLList.nil();
            for (recoder.java.reference.TypeReference tr : arg.getMethodContext().getParamTypes()) {
                TypeReference keyTR = convert(tr);
                paramTypes = paramTypes.append(keyTR.getKeYJavaType());
            }

            methodContext = jInfo.getProgramMethod(classContext.getKeYJavaType(),
                arg.getMethodContext().getMethodName().getText(), paramTypes,
                classContext.getKeYJavaType());
        }

        ReferencePrefix runtimeInstance = null;
        if (arg.getRuntimeInstance() != null) {
            runtimeInstance = (ReferencePrefix) callConvert(arg.getRuntimeInstance());
        }

        return new ExecutionContext(classContext, methodContext, runtimeInstance);
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

    public UnsignedShiftRightAssignment convert(
            recoder.java.expression.operator.UnsignedShiftRightAssignment arg) {
        return new UnsignedShiftRightAssignment(collectChildrenAndComments(arg));
    }

    /**
     * Converts the Negative from recoder to the corresponding KeY JavaProgramElement. If the minus
     * sign belongs to the (decimal) literal, it is included into the literal and the corresponding
     * Int-/LongLiteral is returned. Otherwise a KeY Negative is returned.
     *
     * @param arg the recoder Negative
     * @return a KeY Int-/LongLiteral if the minus sign belongs to the literal or a KeY Negative
     *         otherwise
     */
    public JavaProgramElement convert(recoder.java.expression.operator.Negative arg) {
        /*
         * if the minus surrounds a decimal Int-/LongLiteral -> minus belongs to the literal, no
         * separate javaUnaryMinus(...)
         */
        if (arg.getChildCount() > 0) {
            if (arg.getChildAt(0) instanceof recoder.java.expression.literal.IntLiteral) {
                recoder.java.expression.literal.IntLiteral lit =
                    (recoder.java.expression.literal.IntLiteral) arg.getChildAt(0);
                // decimal: unary minus belongs to the literal
                if (AbstractIntegerLiteral.representsDecLiteral(lit.getValue())) {
                    // encode the minus into the literal
                    return new IntLiteral(collectComments(lit), "-" + lit.getValue());
                }
            } else if (arg.getChildAt(0) instanceof recoder.java.expression.literal.LongLiteral) {
                recoder.java.expression.literal.LongLiteral lit =
                    (recoder.java.expression.literal.LongLiteral) arg.getChildAt(0);
                // decimal: unary minus belongs to the literal
                if (AbstractIntegerLiteral.representsDecLiteral(lit.getValue())) {
                    // encode the minus into the literal
                    return new LongLiteral(collectComments(lit), "-" + lit.getValue());
                }
            }
        }
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

    public TwoState convert(de.uka.ilkd.key.java.recoderext.TwoState m) {
        return new TwoState(collectComments(m));
    }

    public NoState convert(de.uka.ilkd.key.java.recoderext.NoState m) {
        return new NoState(collectComments(m));
    }

    public EmptyStatement convert(recoder.java.statement.EmptyStatement m) {
        return new EmptyStatement(collectChildrenAndComments(m));
    }

    // modifiers

    public Abstract convert(recoder.java.declaration.modifier.Abstract m) {
        return new Abstract(collectChildrenAndComments(m));
    }

    public Public convert(recoder.java.declaration.modifier.Public m) {
        return new Public(collectChildrenAndComments(m));
    }

    public Protected convert(recoder.java.declaration.modifier.Protected m) {
        return new Protected(collectChildrenAndComments(m));
    }

    public Private convert(recoder.java.declaration.modifier.Private m) {
        return new Private(collectChildrenAndComments(m));
    }

    public Static convert(recoder.java.declaration.modifier.Static m) {
        return new Static(collectChildrenAndComments(m));
    }

    public Final convert(recoder.java.declaration.modifier.Final m) {
        return new Final(collectChildrenAndComments(m));
    }

    public StrictFp convert(recoder.java.declaration.modifier.StrictFp m) {
        return new StrictFp(collectChildrenAndComments(m));
    }

    // package reference
    public PackageReference convert(recoder.java.reference.PackageReference m) {
        return new PackageReference(collectChildrenAndComments(m));
    }

}
