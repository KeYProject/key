// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.java;

import java.util.*;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.*;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.java.recoderext.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class creates the <code>&lt;createArray&gt;</code> method for array
 * creation and in particular its helper method
 * <code>&lt;createArrayHelper&gt;</code>. This class should be replaced by a
 * recoder transformation as soon as we port our array data structures to
 * RecodeR.
 */
public final class CreateArrayMethodBuilder extends KeYJavaASTFactory {

    public static final String  IMPLICIT_ARRAY_CREATE                    = "<createArray>";

    public static final String  IMPLICIT_ARRAY_CREATION_HELPER           = "<createArrayHelper>";

    // as these methods are thought to be only preliminary(we cache some
    // information here)
    private final Map<String, ProgramVariable> cache = 
        new LinkedHashMap<String, ProgramVariable>(3);

    /**
     * keeps the currently used integer type
     */
    private final KeYJavaType integerType;

    /**
     * stores the currently used object type
     */
    private final KeYJavaType objectType;
    
    private final Sort heapSort;
    
    private final int heapCount;
    
    

    /** create the method builder for array implict creation methods */
    public CreateArrayMethodBuilder(KeYJavaType integerType,
            			    KeYJavaType objectType,
            			    Sort heapSort,
            			    int heapCount) {
        this.integerType = integerType;
        this.objectType = objectType;
        this.heapSort = heapSort;
        this.heapCount = heapCount;
    }

    /**
     * creates the statements which take the next object out of the list of
     * available objects
     * 
     * @return the statements which take the next object out of the list of
     *         available objects
     */
    protected List<Statement> createArray(ImmutableList<Field> fields) {
        LinkedList<Statement> result = new LinkedList<Statement>();
        ImmutableList<Field> implicitFields = filterImplicitFields(fields);

        // declared only in Object so we have to look there
        ProgramVariable initialized = findInObjectFields(ImplicitFieldAdder.IMPLICIT_INITIALIZED);
        if (initialized == null) {
            // only if createObject for Object is called
            initialized = find(ImplicitFieldAdder.IMPLICIT_INITIALIZED,
                    implicitFields);
        } 

        result.addLast(assign(attribute(new ThisReference(), initialized),
                BooleanLiteral.FALSE));
        return result;
    }

    /**
     * extracts all field specifications out of the given list. Therefore it
     * descends into field declarations.
     * 
     * @param list
     *            the ArrayOf<MemberDeclaration> with the members of a type
     *            declaration
     * @return a IList<Field> the includes all field specifications found int the
     *         field declaration of the given list
     */
    protected ImmutableList<Field> filterField(ImmutableArray<MemberDeclaration> list) {
        ImmutableList<Field> result = ImmutableSLList.<Field>nil();
        for (int i = list.size() - 1; i >= 0; i--) {
            MemberDeclaration pe = list.get(i);
            if (pe instanceof FieldDeclaration) {
                result = result.append(filterField((FieldDeclaration) pe));
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
     * @return a IList<Field> the includes all field specifications found int the
     *         field declaration of the given list
     */
    protected final ImmutableList<Field> filterField(FieldDeclaration field) {
        ImmutableList<Field> result = ImmutableSLList.<Field>nil();
        ImmutableArray<FieldSpecification> spec = field.getFieldSpecifications();
        for (int i = spec.size() - 1; i >= 0; i--) {
            result = result.prepend(spec.get(i));
        }
        return result;
    }

    /**
     * extracts all implicit field specifications out of the given list
     * 
     * @param list
     *            the IList<Field> from which the implicit ones have to be
     *            selected
     * @return a list with all implicit fields found in 'list'
     */
    protected ImmutableList<Field> filterImplicitFields(ImmutableList<Field> list) {
        ImmutableList<Field> result = ImmutableSLList.<Field>nil();
        for (Field aList : list) {
            Field field = aList;
            if (field instanceof ImplicitFieldSpecification) {
                result = result.append(field);
            }
        }
        return result;
    }

    /**
     * retrieves a field with the given name out of the list
     * 
     * @param name
     *            a String with the name of the field to be looked for
     * @param fields
     *            the IList<Field> where we have to look for the field
     * @return the program variable of the given name or null if not found
     */
    protected ProgramVariable find(String name, ImmutableList<Field> fields) {
        for (Field field1 : fields) {
            Field field = field1;
            final ProgramVariable fieldVar = (ProgramVariable) field
                    .getProgramVariable();
            if (name.equals(fieldVar.getProgramElementName().getProgramName())) {
                return fieldVar;
            }
        }
        return null;
    }

    protected ProgramVariable findInObjectFields(String name) {
        ProgramVariable var = cache.get(name);
        if (var == null && objectType.getJavaType() != null) {
            final ImmutableList<Field> objectFields = filterImplicitFields(filterField(((ClassDeclaration) objectType
                    .getJavaType()).getMembers()));
//            final ListOfField objectFields = filterField(((ClassDeclaration) objectType
//                    .getJavaType()).getMembers());
            var = find(name, objectFields);
            if (var != null) { // may be null if object is currently created
                cache.put(name, var);
            }
        }
        return var;
    }

    // ================ HELPER METHODS =========================

    /**
     * creates the implicit method <code>&lt;allocate&gt;</code> which is a
     * stump and given meaning by a contract
     */
    public IProgramMethod getArrayInstanceAllocatorMethod(
            TypeReference arrayTypeReference) {

        final Modifier[] modifiers = new Modifier[] { new Private(),
                new Static() };

        final KeYJavaType arrayType = arrayTypeReference.getKeYJavaType();
        
        final ProgramVariable paramLength = new LocationVariable(
                new ProgramElementName("length"), integerType);

        final ParameterDeclaration param = new ParameterDeclaration(
                new Modifier[0], new TypeRef(integerType),
                new VariableSpecification(paramLength), false);

        final MethodDeclaration md = new MethodDeclaration(
                modifiers,
                arrayTypeReference,
                new ProgramElementName(
                        InstanceAllocationMethodBuilder.IMPLICIT_INSTANCE_ALLOCATE),
                new ParameterDeclaration[]{param}, null, null, false);

        return new ProgramMethod(md, 
        			 arrayType, 
        			 arrayType,
        			 PositionInfo.UNDEFINED,
        			 heapSort,
        			 heapCount);
    }

    protected StatementBlock getCreateArrayBody(TypeReference arrayRef,
             ProgramVariable paramLength) {

        
        
        final LocalVariableDeclaration local = 
            declare(new ProgramElementName("newObject"), arrayRef);
        final ProgramVariable newObject = (ProgramVariable) local
                .getVariables().get(0)
                .getProgramVariable();
        final LinkedList<Statement> body = new LinkedList<Statement>();

        body.addLast(local);
        body.addLast(assign(
                        newObject,
                        new MethodReference(
                                new ImmutableArray<Expression>(paramLength),
                                new ProgramElementName(
                                        InstanceAllocationMethodBuilder.IMPLICIT_INSTANCE_ALLOCATE),
                                arrayRef)));
       
        body.add(new MethodReference(
                        new ImmutableArray<Expression>(),
                        new ProgramElementName(
                                CreateArrayMethodBuilder.IMPLICIT_ARRAY_CREATION_HELPER),
                        newObject));

        body.add(new Return(newObject));

        return new StatementBlock(body.toArray(new Statement[body.size()]));
    }

    /**
     * creates the body of method <code>&lt;createArrayHelper(int
     * paramLength)&gt;</code>
     * therefore it first adds the statements responsible to take the correct
     * one out of the list, then the arrays length attribute is set followed by
     * a call to <code>&lt;prepare&gt;()</code> setting the arrays fields on
     * their default value.
     * 
     * @param length
     *            the final public ProgramVariable
     *            <code>length</length> of the array 
     * @param fields the IList<Fields> of the current array
     * @param createTransient a boolean indicating if a transient array has 
     * to be created (this is special to JavaCard)
     * @param transientType a ProgramVariable identifying the kind of transient
     * @return the StatementBlock which is the method's body <br></br>
     *     <code>
     *  {
     *    this.<nextToCreate> = this.<nextToCreate>.;
     *    this.<initialized> = false;
     *    this.<created>     = true;
     *    this.<prepare>();
     *    this.<transient> = transientType;
     *    this.<initialized> = true;
     *    return this;
     *   }
     *   </code>
     */
    protected StatementBlock getCreateArrayHelperBody(ProgramVariable length,
            ImmutableList<Field> fields,
            boolean createTransient, ProgramVariable transientType) {
	assert !createTransient;

        final ThisReference thisRef = new ThisReference();

        final List<Statement> body = createArray(fields);

        body.add(new MethodReference(new ImmutableArray<Expression>(),
                new ProgramElementName(
                        PrepareObjectBuilder.IMPLICIT_OBJECT_PREPARE), null));

        body.add(assign(attribute(thisRef,
                findInObjectFields(ImplicitFieldAdder.IMPLICIT_INITIALIZED)),
                BooleanLiteral.TRUE));
        
        body.add(new Return(thisRef));

        return new StatementBlock(body.toArray(new Statement[body.size()]));
    }

    /**
     * create the method declaration of the
     * <code>&lt;createArrayHelper&gt;</code> method
     */
    public IProgramMethod getCreateArrayHelperMethod(
            TypeReference arrayTypeReference, ProgramVariable length,
            ImmutableList<Field> fields) {

        final Modifier[] modifiers = new Modifier[] { new Private()};
        final KeYJavaType arrayType = arrayTypeReference.getKeYJavaType();

        final MethodDeclaration md = new MethodDeclaration(modifiers,
                arrayTypeReference, new ProgramElementName(
                        IMPLICIT_ARRAY_CREATION_HELPER),
                new ParameterDeclaration[0], null,
                getCreateArrayHelperBody(length, fields, false,
                        null), false);

        return new ProgramMethod(md, 
        			 arrayType, 
        			 arrayType,
        			 PositionInfo.UNDEFINED,
        			 heapSort,
        			 heapCount);
    }

    /**
     * creates the implicit method <code>&lt;createArray&gt;</code> it
     * fulfills a similar purpose as <code>&lt;createObject&gt;</code> in
     * addition it sets the arrays length and calls the prepare method
     */
    public IProgramMethod getCreateArrayMethod(TypeReference arrayTypeReference,
            IProgramMethod prepare, ImmutableList<Field> fields) {

        final Modifier[] modifiers = new Modifier[] { new Protected(),
                new Static() };

        final KeYJavaType arrayType = arrayTypeReference.getKeYJavaType();

        final ProgramVariable paramLength = new LocationVariable(
                new ProgramElementName("length"), integerType);

        final ParameterDeclaration param = new ParameterDeclaration(
                new Modifier[0], new TypeRef(integerType),
                new VariableSpecification(paramLength), false);

        final MethodDeclaration md = new MethodDeclaration(modifiers,
                arrayTypeReference, new ProgramElementName(
                        IMPLICIT_ARRAY_CREATE),
                new ParameterDeclaration[] { param }, null,                 
                getCreateArrayBody(arrayTypeReference, paramLength), false);

        return new ProgramMethod(md, 
        			 arrayType, 
        			 arrayType,
        			 PositionInfo.UNDEFINED,
        			 heapSort,
        			 heapCount);
    }

    /**
     * returns the default value of the given type according to JLS \S 4.5.5
     * 
     * @return the default value of the given type according to JLS \S 4.5.5
     */
    protected Expression getDefaultValue(Type type) {
        if (type instanceof PrimitiveType) {
            return type.getDefaultValue();
        }
        return NullLiteral.NULL;
    }

    /**
     * returns the prepare method for arrays initialising all array fields with
     * their default value
     */
    public IProgramMethod getPrepareArrayMethod(TypeRef arrayRef,
            ProgramVariable length, Expression defaultValue, ImmutableList<Field> fields) {

        final KeYJavaType arrayType = arrayRef.getKeYJavaType();

        final IntLiteral zero = new IntLiteral(0);

        
        final LocalVariableDeclaration forInit = KeYJavaASTFactory.
        declare(new ProgramElementName("i"), zero, integerType);

        final ProgramVariable pv = (ProgramVariable) forInit.getVariables()
                .get(0).getProgramVariable();

        final For forLoop = new For(new LoopInitializer[] { forInit },
                new LessThan(pv,
                        new FieldReference(length, new ThisReference())),
                new Expression[] { new PostIncrement(pv) }, assign(
                        new ArrayReference(new ThisReference(),
                                new Expression[] { pv }), defaultValue));

        final StatementBlock body = new StatementBlock(
                new Statement[] { forLoop });

        final MethodDeclaration md = new MethodDeclaration(
                new Modifier[] { new Private()}, arrayRef,
                new ProgramElementName(
                        PrepareObjectBuilder.IMPLICIT_OBJECT_PREPARE),
                new ParameterDeclaration[0], null, body, false);

        return new ProgramMethod(md, 
        	                 arrayType, 
        			 KeYJavaType.VOID_TYPE,
        			 PositionInfo.UNDEFINED,
        			 heapSort);
    }

}
