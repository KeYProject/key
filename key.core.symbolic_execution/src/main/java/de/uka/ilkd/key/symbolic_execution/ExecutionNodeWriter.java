/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.Charset;
import java.util.Arrays;
import java.util.Map;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionAuxiliaryContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBaseMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBlockStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionElement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionExceptionalMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionJoin;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLink;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturnValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.util.LinkedHashMap;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.ArrayUtil;

/**
 * Allows to persistent selected properties of {@link IExecutionNode}s as XML file. Such files can
 * be read via an {@link ExecutionNodeReader} instance.
 *
 * @author Martin Hentschel
 * @see ExecutionNodeReader
 */
public class ExecutionNodeWriter extends AbstractWriter {
    /**
     * Attribute name to store {@link IExecutionElement#getName()}.
     */
    public static final String ATTRIBUTE_NAME = "name";

    /**
     * Attribute name to store {@link IExecutionMethodReturn#getNameIncludingReturnValue()}.
     */
    public static final String ATTRIBUTE_NAME_INCLUDING_RETURN_VALUE = "nameIncludingReturnValue";

    /**
     * Attribute name to store {@link IExecutionMethodReturn#getSignatureIncludingReturnValue()}.
     */
    public static final String ATTRIBUTE_SIGNATURE_INCLUDING_RETURN_VALUE =
        "signatureIncludingReturnValue";

    /**
     * Attribute name to store {@link IExecutionMethodReturn#getSignature()}.
     */
    public static final String ATTRIBUTE_SIGNATURE = "signature";

    /**
     * Attribute exceptional termination to store
     * {@link IExecutionTermination#getTerminationKind()}.
     */
    public static final String ATTRIBUTE_TERMINATION_KIND = "terminationKind";

    /**
     * Attribute name to store {@link IExecutionVariable#getTypeString()}.
     */
    public static final String ATTRIBUTE_TYPE_STRING = "typeString";

    /**
     * Attribute name to store {@link IExecutionVariable#getValueString()}.
     */
    public static final String ATTRIBUTE_VALUE_STRING = "valueString";

    /**
     * Attribute name to store {@link IExecutionValue#getConditionString()}.
     */
    public static final String ATTRIBUTE_CONDITION_STRING = "conditionString";

    /**
     * Attribute name to store {@link IExecutionMethodReturnValue#getReturnValueString()}.
     */
    public static final String ATTRIBUTE_RETURN_VALUE_STRING = "returnValueString";

    /**
     * Attribute name to store {@link IExecutionMethodReturnValue#hasCondition()}.
     */
    public static final String ATTRIBUTE_HAS_CONDITION = "hasCondition";

    /**
     * Attribute name to store {@link IExecutionTermination#isBranchVerified()}.
     */
    public static final String ATTRIBUTE_BRANCH_VERIFIED = "branchVerified";

    /**
     * Attribute name to store {@link IExecutionVariable#getArrayIndexString()}.
     */
    public static final String ATTRIBUTE_ARRAY_INDEX = "arrayIndex";

    /**
     * Attribute name to store {@link IExecutionVariable#isArrayIndex()}.
     */
    public static final String ATTRIBUTE_IS_ARRAY_INDEX = "isArrayIndex";

    /**
     * Attribute name to store {@link IExecutionBranchCondition#getFormatedBranchCondition()}.
     */
    public static final String ATTRIBUTE_BRANCH_CONDITION = "branchCondition";

    /**
     * Attribute name to store {@link IExecutionNode#getPathCondition()}.
     */
    public static final String ATTRIBUTE_PATH_CONDITION = "pathCondition";

    /**
     * Attribute name to store {@link IExecutionNode#isPathConditionChanged()}.
     */
    public static final String ATTRIBUTE_PATH_CONDITION_CHANGED = "pathConditionChanged";

    /**
     * A path which refers to an {@link IExecutionNode} starting from the root.
     */
    public static final String ATTRIBUTE_PATH_IN_TREE = "path";

    /**
     * Attribute name to store {@link IExecutionBranchCondition#isMergedBranchCondition()}.
     */
    public static final String ATTRIBUTE_MERGED_BRANCH_CONDITION = "mergedBranchCondition";

    /**
     * Attribute name to store {@link IExecutionVariable#isValueAnObject()}.
     */
    public static final String ATTRIBUTE_IS_VALUE_AN_OBJECT = "isValueAnObject";

    /**
     * Attribute name to store {@link IExecutionVariable#isValueUnknown()}.
     */
    public static final String ATTRIBUTE_IS_VALUE_UNKNOWN = "isValueUnknown";

    /**
     * Attribute name to store {@link IExecutionOperationContract#isPreconditionComplied()}.
     */
    public static final String ATTRIBUTE_PRECONDITION_COMPLIED = "preconditionComplied";

    /**
     * Attribute name to store {@link IExecutionOperationContract#hasNotNullCheck()}.
     */
    public static final String ATTRIBUTE_HAS_NOT_NULL_CHECK = "hasNotNullCheck";

    /**
     * Attribute name to store {@link IExecutionMethodReturn#isReturnValuesComputed()}.
     */
    public static final String ATTRIBUTE_RETURN_VALUE_COMPUTED = "isReturnValueComputed";

    /**
     * Attribute name to store {@link IExecutionBranchCondition#isBranchConditionComputed()}.
     */
    public static final String ATTRIBUTE_BRANCH_CONDITION_COMPUTED = "isBranchConditionComputed";

    /**
     * Attribute name to store {@link IExecutionOperationContract#isNotNullCheckComplied()}.
     */
    public static final String ATTRIBUTE_NOT_NULL_CHECK_COMPLIED = "notNullCheckComplied";

    /**
     * Attribute name to store {@link IExecutionLoopInvariant#isInitiallyValid()}.
     */
    public static final String ATTRIBUTE_INITIALLY_VALID = "initiallyValid";

    /**
     * Attribute name to store {@link IExecutionBranchCondition#getAdditionalBranchLabel()}.
     */
    public static final String ATTRIBUTE_ADDITIONAL_BRANCH_LABEL = "additionalBranchLabel";

    /**
     * Attribute name to store {@link IExecutionMethodReturn#getMethodReturnCondition()}.
     */
    public static final String ATTRIBUTE_METHOD_RETURN_CONDITION = "methodReturnCondition";

    /**
     * Attribute name to store {@link IExecutionOperationContract#getFormatedResultTerm()}.
     */
    public static final String ATTRIBUTE_RESULT_TERM = "resultTerm";

    /**
     * Attribute name to store {@link IExecutionOperationContract#getFormatedExceptionTerm()}.
     */
    public static final String ATTRIBUTE_EXCEPTION_TERM = "exceptionTerm";

    /**
     * Attribute name to store {@link IExecutionOperationContract#getFormatedSelfTerm()}.
     */
    public static final String ATTRIBUTE_SELF_TERM = "selfTerm";

    /**
     * Attribute name to store {@link IExecutionOperationContract#getFormatedContractParams()}.
     */
    public static final String ATTRIBUTE_CONTRACT_PARAMETERS = "contractParameters";

    /**
     * Attribute name to store {@link IExecutionBlockStartNode#isBlockOpened()}.
     */
    public static final String ATTRIBUTE_BLOCK_OPENED = "blockOpened";

    /**
     * Attribute name to store {@link IExecutionJoin#isWeakeningVerified()}.
     */
    public static final String ATTRIBUTE_WEAKENING_VERIFIED = "weakeningVerified";

    /**
     * Tag name to store {@link IExecutionBranchCondition}s.
     */
    public static final String TAG_BRANCH_CONDITION = "branchCondition";

    /**
     * Tag name to store {@link IExecutionStart}s.
     */
    public static final String TAG_START = "start";

    /**
     * Tag name to store {@link IExecutionBranchStatement}s.
     */
    public static final String TAG_BRANCH_STATEMENT = "branchStatement";

    /**
     * Tag name to store {@link IExecutionLoopCondition}s.
     */
    public static final String TAG_LOOP_CONDITION = "loopCondition";

    /**
     * Tag name to store {@link IExecutionLoopStatement}s.
     */
    public static final String TAG_LOOP_STATEMENT = "loopStatement";

    /**
     * Tag name to store {@link IExecutionMethodCall}s.
     */
    public static final String TAG_METHOD_CALL = "methodCall";

    /**
     * Tag name to store {@link IExecutionMethodReturn}s.
     */
    public static final String TAG_METHOD_RETURN = "methodReturn";

    /**
     * Tag name to store {@link IExecutionExceptionalMethodReturn}s.
     */
    public static final String TAG_EXCEPTIONAL_METHOD_RETURN = "exceptionalMethodReturn";

    /**
     * Tag name to store {@link IExecutionMethodReturnValue}s.
     */
    public static final String TAG_METHOD_RETURN_VALUE = "methodReturnValue";

    /**
     * Tag name to store {@link IExecutionStatement}s.
     */
    public static final String TAG_STATEMENT = "statement";

    /**
     * Tag name to store {@link IExecutionTermination}s.
     */
    public static final String TAG_TERMINATION = "termination";

    /**
     * Tag name to store {@link IExecutionJoin}s.
     */
    public static final String TAG_JOIN = "join";

    /**
     * Tag name to store {@link IExecutionOperationContract}s.
     */
    public static final String TAG_OPERATION_CONTRACT = "operationContract";

    /**
     * Tag name to store {@link IExecutionAuxiliaryContract}s.
     */
    public static final String TAG_BLOCK_CONTRACT = "blockContract";

    /**
     * Tag name to store {@link IExecutionLoopInvariant}s.
     */
    public static final String TAG_LOOP_INVARIANT = "loopInvariant";

    /**
     * Tag name to store {@link IExecutionConstraint}s.
     */
    public static final String TAG_CONSTRAINT = "constraint";

    /**
     * Tag name to store {@link IExecutionVariable}s.
     */
    public static final String TAG_VARIABLE = "variable";

    /**
     * Tag name to store call state {@link IExecutionVariable}s.
     */
    public static final String TAG_CALL_STATE_VARIABLE = "callStateVariable";

    /**
     * Tag name to store {@link IExecutionValue}s.
     */
    public static final String TAG_VALUE = "value";

    /**
     * Tag name to store one entry of {@link IExecutionNode#getCallStack()}.
     */
    public static final String TAG_CALL_STACK_ENTRY = "callStackEntry";

    /**
     * Tag name to store one entry of {@link IExecutionMethodCall#getMethodReturns()}.
     */
    public static final String TAG_METHOD_RETURN_ENTRY = "methodReturnEntry";

    /**
     * Tag name to store on entry of {@link IExecutionNode#getCompletedBlocks()} together with its
     * condition {@link IExecutionNode#getFormatedBlockCompletionCondition(IExecutionNode)}.
     */
    public static final String TAG_COMPLETED_BLOCK_ENTRY = "completedBlockEntry";

    /**
     * Tag name to store one entry of {@link IExecutionBranchStatement#getBlockCompletions()}.
     */
    public static final String TAG_BLOCK_COMPLETION_ENTRY = "blockCompletionEntry";

    /**
     * Tag name to store one entry of {@link IExecutionStart#getTerminations()}.
     */
    public static final String TAG_TERMINATION_ENTRY = "terminationEntry";

    /**
     * Tag name to store one entry of {@link IExecutionNode#getOutgoingLinks()}.
     */
    public static final String TAG_OUTGOING_LINK = "outgoingLink";

    /**
     * Character to separate path entries in attributes {@value #ATTRIBUTE_PATH_IN_TREE}.
     */
    public static final char PATH_SEPARATOR = '/';

    /**
     * Writes the given {@link IExecutionNode} as XML file.
     *
     * @param node The {@link IExecutionNode} to save.
     * @param encoding The encoding to use.
     * @param file The {@link File} to save to.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @throws IOException Occurred Exception.
     * @throws ProofInputException Occurred Exception.
     */
    public void write(IExecutionNode<?> node, String encoding, File file, boolean saveVariables,
            boolean saveCallStack, boolean saveReturnValues, boolean saveConstraints)
            throws IOException, ProofInputException {
        try (var out = new FileOutputStream(file)) {
            write(node, encoding, out, saveVariables, saveCallStack,
                saveReturnValues, saveConstraints);
        }
    }

    /**
     * Writes the given {@link IExecutionNode} into the {@link OutputStream}.
     *
     * @param node The {@link IExecutionNode} to save.
     * @param encoding The encoding to use.
     * @param out The {@link OutputStream} to save to. The {@link OutputStream} will be closed by
     *        this method.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @throws IOException Occurred Exception.
     * @throws ProofInputException Occurred Exception.
     */
    public void write(IExecutionNode<?> node, String encoding, OutputStream out,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints) throws IOException, ProofInputException {
        if (out != null) {
            Charset charset =
                encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(node, charset.displayName(), saveVariables, saveCallStack,
                saveReturnValues, saveConstraints);
            out.write(xml.getBytes(charset));
        }
    }

    /**
     * Converts the given {@link IExecutionNode} into XML.
     *
     * @param node The {@link IExecutionNode} to convert.
     * @param encoding The encoding to use.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @return The created XML content.
     * @throws ProofInputException Occurred Exception.
     */
    public String toXML(IExecutionNode<?> node, String encoding, boolean saveVariables,
            boolean saveCallStack, boolean saveReturnValues, boolean saveConstraints)
            throws ProofInputException {
        StringBuilder sb = new StringBuilder();
        appendXmlHeader(encoding, sb);
        appendExecutionNode(0, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        return sb.toString();
    }

    /**
     * Converts the given {@link IExecutionNode} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionNode} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionNode(int level, IExecutionNode<?> node, boolean saveVariables,
            boolean saveCallStack, boolean saveReturnValues, boolean saveConstraints,
            StringBuilder sb) throws ProofInputException {
        if (node instanceof IExecutionBranchCondition) {
            appendExecutionBranchCondition(level, (IExecutionBranchCondition) node, saveVariables,
                saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionStart) {
            appendExecutionStart(level, (IExecutionStart) node, saveVariables, saveCallStack,
                saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionBranchStatement) {
            appendExecutionBranchStatement(level, (IExecutionBranchStatement) node, saveVariables,
                saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionLoopCondition) {
            appendExecutionLoopCondition(level, (IExecutionLoopCondition) node, saveVariables,
                saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionLoopStatement) {
            appendExecutionLoopStatement(level, (IExecutionLoopStatement) node, saveVariables,
                saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionMethodCall) {
            appendExecutionMethodCall(level, (IExecutionMethodCall) node, saveVariables,
                saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionMethodReturn) {
            appendExecutionMethodReturn(level, (IExecutionMethodReturn) node, saveVariables,
                saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionExceptionalMethodReturn) {
            appendExecutionExceptionalMethodReturn(level, (IExecutionExceptionalMethodReturn) node,
                saveVariables, saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionStatement) {
            appendExecutionStatement(level, (IExecutionStatement) node, saveVariables,
                saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionTermination) {
            appendExecutionTermination(level, (IExecutionTermination) node, saveVariables,
                saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionOperationContract) {
            appendExecutionOperationContract(level, (IExecutionOperationContract) node,
                saveVariables, saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionLoopInvariant) {
            appendExecutionLoopInvariant(level, (IExecutionLoopInvariant) node, saveVariables,
                saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionAuxiliaryContract) {
            appendExecutionBlockContract(level, (IExecutionAuxiliaryContract) node, saveVariables,
                saveCallStack, saveReturnValues, saveConstraints, sb);
        } else if (node instanceof IExecutionJoin) {
            appendExecutionJoin(level, (IExecutionJoin) node, saveVariables, saveCallStack,
                saveReturnValues, saveConstraints, sb);
        } else {
            throw new IllegalArgumentException("Not supported node \"" + node + "\".");
        }
    }

    /**
     * Converts the given {@link IExecutionBranchCondition} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionBranchCondition} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionBranchCondition(int level, IExecutionBranchCondition node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        attributeValues.put(ATTRIBUTE_BRANCH_CONDITION, node.getFormatedBranchCondition());
        attributeValues.put(ATTRIBUTE_MERGED_BRANCH_CONDITION, node.isMergedBranchCondition() + "");
        attributeValues.put(ATTRIBUTE_BRANCH_CONDITION_COMPUTED,
            node.isBranchConditionComputed() + "");
        attributeValues.put(ATTRIBUTE_ADDITIONAL_BRANCH_LABEL, node.getAdditionalBranchLabel());
        appendStartTag(level, TAG_BRANCH_CONDITION, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendEndTag(level, TAG_BRANCH_CONDITION, sb);
    }

    /**
     * Converts the given {@link IExecutionStart} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionStart} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionStart(int level, IExecutionStart node, boolean saveVariables,
            boolean saveCallStack, boolean saveReturnValues, boolean saveConstraints,
            StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        appendStartTag(level, TAG_START, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendTerminations(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendEndTag(level, TAG_START, sb);
    }

    /**
     * Appends the termination entries to the given {@link StringBuilder}.
     *
     * @param level The level of the children.
     * @param node The {@link IExecutionStart} which provides the termination entries.
     * @param sb The {@link StringBuilder} to append to.
     */
    protected void appendTerminations(int level, IExecutionStart node, StringBuilder sb) {
        ImmutableList<IExecutionTermination> terminations = node.getTerminations();
        if (terminations != null) {
            for (IExecutionTermination termination : terminations) {
                Map<String, String> attributeValues = new LinkedHashMap<>();
                attributeValues.put(ATTRIBUTE_PATH_IN_TREE, computePath(termination));
                appendEmptyTag(level, TAG_TERMINATION_ENTRY, attributeValues, sb);
            }
        }
    }

    /**
     * Converts the given {@link IExecutionLoopCondition} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionLoopCondition} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionBranchStatement(int level, IExecutionBranchStatement node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        attributeValues.put(ATTRIBUTE_BLOCK_OPENED, node.isBlockOpened() + "");
        appendStartTag(level, TAG_BRANCH_STATEMENT, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendBlockCompletions(level + 1, node, sb);
        appendEndTag(level, TAG_BRANCH_STATEMENT, sb);
    }

    /**
     * Converts the given {@link IExecutionLoopCondition} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionLoopCondition} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionLoopCondition(int level, IExecutionLoopCondition node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        attributeValues.put(ATTRIBUTE_BLOCK_OPENED, node.isBlockOpened() + "");
        appendStartTag(level, TAG_LOOP_CONDITION, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendBlockCompletions(level + 1, node, sb);
        appendEndTag(level, TAG_LOOP_CONDITION, sb);
    }

    /**
     * Converts the given {@link IExecutionLoopStatement} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionLoopStatement} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionLoopStatement(int level, IExecutionLoopStatement node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        attributeValues.put(ATTRIBUTE_BLOCK_OPENED, node.isBlockOpened() + "");
        appendStartTag(level, TAG_LOOP_STATEMENT, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendBlockCompletions(level + 1, node, sb);
        appendEndTag(level, TAG_LOOP_STATEMENT, sb);
    }

    /**
     * Converts the given {@link IExecutionMethodCall} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionMethodCall} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionMethodCall(int level, IExecutionMethodCall node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        appendStartTag(level, TAG_METHOD_CALL, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendMethodReturns(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendEndTag(level, TAG_METHOD_CALL, sb);
    }

    /**
     * Converts the given {@link IExecutionMethodReturn} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionMethodReturn} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionMethodReturn(int level, IExecutionMethodReturn node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_SIGNATURE, node.getSignature());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        if (saveReturnValues) {
            attributeValues.put(ATTRIBUTE_NAME_INCLUDING_RETURN_VALUE,
                node.getNameIncludingReturnValue());
            attributeValues.put(ATTRIBUTE_SIGNATURE_INCLUDING_RETURN_VALUE,
                node.getSignatureIncludingReturnValue());
        }
        attributeValues.put(ATTRIBUTE_RETURN_VALUE_COMPUTED, node.isReturnValuesComputed() + "");
        attributeValues.put(ATTRIBUTE_METHOD_RETURN_CONDITION,
            node.getFormatedMethodReturnCondition());
        appendStartTag(level, TAG_METHOD_RETURN, attributeValues, sb);
        if (saveReturnValues) {
            IExecutionMethodReturnValue[] returnValues = node.getReturnValues();
            for (IExecutionMethodReturnValue returnValue : returnValues) {
                appendExecutionMethodReturnValue(level + 1, returnValue, sb);
            }
        }
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendCallStateVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendEndTag(level, TAG_METHOD_RETURN, sb);
    }

    /**
     * Converts the given {@link IExecutionExceptionalMethodReturn} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionExceptionalMethodReturn} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionExceptionalMethodReturn(int level,
            IExecutionExceptionalMethodReturn node, boolean saveVariables, boolean saveCallStack,
            boolean saveReturnValues, boolean saveConstraints, StringBuilder sb)
            throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_SIGNATURE, node.getSignature());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        attributeValues.put(ATTRIBUTE_METHOD_RETURN_CONDITION,
            node.getFormatedMethodReturnCondition());
        appendStartTag(level, TAG_EXCEPTIONAL_METHOD_RETURN, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendCallStateVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendEndTag(level, TAG_EXCEPTIONAL_METHOD_RETURN, sb);
    }

    /**
     * Converts the given {@link IExecutionMethodReturnValue} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param returnValue The {@link IExecutionMethodReturnValue} to convert.
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionMethodReturnValue(int level,
            IExecutionMethodReturnValue returnValue, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, returnValue.getName());
        attributeValues.put(ATTRIBUTE_RETURN_VALUE_STRING, returnValue.getReturnValueString());
        attributeValues.put(ATTRIBUTE_HAS_CONDITION, returnValue.hasCondition() + "");
        attributeValues.put(ATTRIBUTE_CONDITION_STRING, returnValue.getConditionString());
        appendStartTag(level, TAG_METHOD_RETURN_VALUE, attributeValues, sb);
        appendEndTag(level, TAG_METHOD_RETURN_VALUE, sb);
    }

    /**
     * Converts the given {@link IExecutionStatement} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionStatement} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionStatement(int level, IExecutionStatement node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        appendStartTag(level, TAG_STATEMENT, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendEndTag(level, TAG_STATEMENT, sb);
    }

    /**
     * Converts the given {@link IExecutionJoin} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionJoin} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionJoin(int level, IExecutionJoin node, boolean saveVariables,
            boolean saveCallStack, boolean saveReturnValues, boolean saveConstraints,
            StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        attributeValues.put(ATTRIBUTE_WEAKENING_VERIFIED, node.isWeakeningVerified() + "");
        appendStartTag(level, TAG_JOIN, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendEndTag(level, TAG_JOIN, sb);
    }

    /**
     * Converts the given {@link IExecutionOperationContract} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionOperationContract} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionOperationContract(int level, IExecutionOperationContract node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        attributeValues.put(ATTRIBUTE_RESULT_TERM, node.getFormatedResultTerm());
        attributeValues.put(ATTRIBUTE_EXCEPTION_TERM, node.getFormatedExceptionTerm());
        attributeValues.put(ATTRIBUTE_SELF_TERM, node.getFormatedSelfTerm());
        attributeValues.put(ATTRIBUTE_CONTRACT_PARAMETERS, node.getFormatedContractParams());

        attributeValues.put(ATTRIBUTE_PRECONDITION_COMPLIED, node.isPreconditionComplied() + "");
        attributeValues.put(ATTRIBUTE_HAS_NOT_NULL_CHECK, node.hasNotNullCheck() + "");
        attributeValues.put(ATTRIBUTE_NOT_NULL_CHECK_COMPLIED, node.isNotNullCheckComplied() + "");

        appendStartTag(level, TAG_OPERATION_CONTRACT, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendEndTag(level, TAG_OPERATION_CONTRACT, sb);
    }

    /**
     * Converts the given {@link IExecutionLoopInvariant} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionLoopInvariant} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionLoopInvariant(int level, IExecutionLoopInvariant node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");

        attributeValues.put(ATTRIBUTE_INITIALLY_VALID, node.isInitiallyValid() + "");

        appendStartTag(level, TAG_LOOP_INVARIANT, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendEndTag(level, TAG_LOOP_INVARIANT, sb);
    }

    /**
     * Converts the given {@link IExecutionAuxiliaryContract} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionLoopInvariant} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionBlockContract(int level, IExecutionAuxiliaryContract node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");

        attributeValues.put(ATTRIBUTE_PRECONDITION_COMPLIED, node.isPreconditionComplied() + "");

        appendStartTag(level, TAG_BLOCK_CONTRACT, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendEndTag(level, TAG_BLOCK_CONTRACT, sb);
    }

    /**
     * Converts the given {@link IExecutionTermination} into XML and appends it to the
     * {@link StringBuilder}.
     *
     * @param level The current child level.
     * @param node The {@link IExecutionTermination} to convert.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendExecutionTermination(int level, IExecutionTermination node,
            boolean saveVariables, boolean saveCallStack, boolean saveReturnValues,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, node.getName());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
        attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
        attributeValues.put(ATTRIBUTE_TERMINATION_KIND, node.getTerminationKind().toString());
        attributeValues.put(ATTRIBUTE_BRANCH_VERIFIED, node.isBranchVerified() + "");
        appendStartTag(level, TAG_TERMINATION, attributeValues, sb);
        appendConstraints(level + 1, node, saveConstraints, sb);
        appendVariables(level + 1, node, saveVariables, saveConstraints, sb);
        appendCallStack(level + 1, node, saveCallStack, sb);
        appendChildren(level + 1, node, saveVariables, saveCallStack, saveReturnValues,
            saveConstraints, sb);
        appendOutgoingLinks(level + 1, node, sb);
        appendCompletedBlocks(level + 1, node, sb);
        appendEndTag(level, TAG_TERMINATION, sb);
    }

    /**
     * Appends the contained {@link IExecutionConstraint}s to the given {@link StringBuilder}.
     *
     * @param level The level to use.
     * @param value The {@link IExecutionValue} which provides the {@link IExecutionConstraint}s.
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendConstraints(int level, IExecutionValue value, boolean saveConstraints,
            StringBuilder sb) throws ProofInputException {
        if (saveConstraints) {
            IExecutionConstraint[] constraints = value.getConstraints();
            for (IExecutionConstraint constraint : constraints) {
                appendConstraint(level, constraint, sb);
            }
        }
    }

    /**
     * Appends the contained {@link IExecutionConstraint}s to the given {@link StringBuilder}.
     *
     * @param level The level to use.
     * @param node The {@link IExecutionNode} which provides the {@link IExecutionConstraint}s.
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendConstraints(int level, IExecutionNode<?> node, boolean saveConstraints,
            StringBuilder sb) throws ProofInputException {
        if (saveConstraints) {
            IExecutionConstraint[] constraints = node.getConstraints();
            for (IExecutionConstraint constraint : constraints) {
                appendConstraint(level, constraint, sb);
            }
        }
    }

    /**
     * Appends the given {@link IExecutionConstraint} with its children to the given
     * {@link StringBuilder}.
     *
     * @param level The level to use.
     * @param constraint The {@link IExecutionConstraint} to append.
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendConstraint(int level, IExecutionConstraint constraint, StringBuilder sb)
            throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, constraint.getName());
        appendEmptyTag(level, TAG_CONSTRAINT, attributeValues, sb);
    }

    /**
     * Appends the contained {@link IExecutionVariable}s to the given {@link StringBuilder}.
     *
     * @param level The level to use.
     * @param node The {@link IExecutionNode} which provides the {@link IExecutionVariable}s.
     * @param saveVariables Save variables?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendVariables(int level, IExecutionNode<?> node, boolean saveVariables,
            boolean saveConstraints, StringBuilder sb) throws ProofInputException {
        if (saveVariables) {
            IExecutionVariable[] variables = node.getVariables();
            for (IExecutionVariable variable : variables) {
                appendVariable(level, variable, saveConstraints, TAG_VARIABLE, sb);
            }
        }
    }

    /**
     * Appends the contained {@link IExecutionVariable}s to the given {@link StringBuilder}.
     *
     * @param level The level to use.
     * @param node The {@link IExecutionNode} which provides the {@link IExecutionVariable}s.
     * @param saveVariables Save variables?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendCallStateVariables(int level, IExecutionBaseMethodReturn<?> node,
            boolean saveVariables, boolean saveConstraints, StringBuilder sb)
            throws ProofInputException {
        if (saveVariables) {
            IExecutionVariable[] variables = node.getCallStateVariables();
            for (IExecutionVariable variable : variables) {
                appendVariable(level, variable, saveConstraints, TAG_CALL_STATE_VARIABLE, sb);
            }
        }
    }

    /**
     * Appends the given {@link IExecutionVariable} with its children to the given
     * {@link StringBuilder}.
     *
     * @param level The level to use.
     * @param variable The {@link IExecutionVariable} to append.
     * @param saveConstraints Save constraints?
     * @param tagName The tag name to store an {@link IExecutionVariable}.
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendVariable(int level, IExecutionVariable variable, boolean saveConstraints,
            String tagName, StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, variable.getName());
        attributeValues.put(ATTRIBUTE_ARRAY_INDEX, variable.getArrayIndexString());
        attributeValues.put(ATTRIBUTE_IS_ARRAY_INDEX, variable.isArrayIndex() + "");
        appendStartTag(level, tagName, attributeValues, sb);
        appendValues(level + 1, variable, saveConstraints, sb);
        appendEndTag(level, tagName, sb);
    }

    /**
     * Appends the contained {@link IExecutionValue}s to the given {@link StringBuilder}.
     *
     * @param level The level to use.
     * @param variable The {@link IExecutionVariable} which provides the {@link IExecutionValue}s.
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendValues(int level, IExecutionVariable variable, boolean saveConstraints,
            StringBuilder sb) throws ProofInputException {
        IExecutionValue[] values = variable.getValues();
        for (IExecutionValue value : values) {
            appendValue(level, value, saveConstraints, sb);
        }
    }

    /**
     * Appends the given {@link IExecutionValue} with its children to the given
     * {@link StringBuilder}.
     *
     * @param level The level to use.
     * @param value The {@link IExecutionValue} to append.
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendValue(int level, IExecutionValue value, boolean saveConstraints,
            StringBuilder sb) throws ProofInputException {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_NAME, value.getName());
        attributeValues.put(ATTRIBUTE_TYPE_STRING, value.getTypeString());
        attributeValues.put(ATTRIBUTE_VALUE_STRING, value.getValueString());
        attributeValues.put(ATTRIBUTE_IS_VALUE_AN_OBJECT, value.isValueAnObject() + "");
        attributeValues.put(ATTRIBUTE_IS_VALUE_UNKNOWN, value.isValueUnknown() + "");
        attributeValues.put(ATTRIBUTE_CONDITION_STRING, value.getConditionString());
        appendStartTag(level, TAG_VALUE, attributeValues, sb);
        // Constraints
        appendConstraints(level + 1, value, saveConstraints, sb);
        // Children
        IExecutionVariable[] childVariables = value.getChildVariables();
        for (IExecutionVariable childVariable : childVariables) {
            appendVariable(level + 1, childVariable, saveConstraints, TAG_VARIABLE, sb);
        }
        appendEndTag(level, TAG_VALUE, sb);
    }

    /**
     * Appends the child nodes to the given {@link StringBuilder}.
     *
     * @param childLevel The level of the children.
     * @param parent The parent {@link IExecutionNode} which provides the children.
     * @param saveVariables Save variables?
     * @param saveCallStack Save method call stack?
     * @param saveReturnValues Save method return values?
     * @param saveConstraints Save constraints?
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception.
     */
    protected void appendChildren(int childLevel, IExecutionNode<?> parent, boolean saveVariables,
            boolean saveCallStack, boolean saveReturnValues, boolean saveConstraints,
            StringBuilder sb) throws ProofInputException {
        IExecutionNode<?>[] children = parent.getChildren();
        for (IExecutionNode<?> child : children) {
            appendExecutionNode(childLevel, child, saveVariables, saveCallStack, saveReturnValues,
                saveConstraints, sb);
        }
    }

    /**
     * appends outgoing links to the given StringBuilder
     *
     * @param level the int specifying indentation level
     * @param node the {@link IExecutionNode} whose outgoing links are to be reported
     * @param sb the StringBuilder with the resulting text description
     */
    protected void appendOutgoingLinks(int level, IExecutionNode<?> node, StringBuilder sb) {
        if (!node.getOutgoingLinks().isEmpty()) {
            for (IExecutionLink link : node.getOutgoingLinks()) {
                appendOutgoingLink(level, link, sb);
            }
        }
    }

    /**
     * appends outgoing links to the given StringBuilder
     *
     * @param level the int specifying indentation level
     * @param link the outgoing {@link IExecutionLink} to be reported
     * @param sb the StringBuilder with the resulting text description
     */
    protected void appendOutgoingLink(int level, IExecutionLink link, StringBuilder sb) {
        Map<String, String> attributeValues = new LinkedHashMap<>();
        attributeValues.put(ATTRIBUTE_PATH_IN_TREE, computePath(link.getTarget()));
        appendEmptyTag(level, TAG_OUTGOING_LINK, attributeValues, sb);
    }

    /**
     * Appends the call stack entries if required to the given {@link StringBuilder}.
     *
     * @param level The level of the children.
     * @param node The {@link IExecutionNode} which provides the call stack.
     * @param saveCallStack Defines if the call stack should be saved or not.
     * @param sb The {@link StringBuilder} to append to.
     */
    protected void appendCallStack(int level, IExecutionNode<?> node, boolean saveCallStack,
            StringBuilder sb) {
        if (saveCallStack) {
            IExecutionNode<?>[] callStack = node.getCallStack();
            if (callStack != null) {
                for (IExecutionNode<?> stackNode : callStack) {
                    Map<String, String> attributeValues = new LinkedHashMap<>();
                    attributeValues.put(ATTRIBUTE_PATH_IN_TREE, computePath(stackNode));
                    appendEmptyTag(level, TAG_CALL_STACK_ENTRY, attributeValues, sb);
                }
            }
        }
    }

    /**
     * Appends the method return entries to the given {@link StringBuilder}.
     *
     * @param level The level of the children.
     * @param node The {@link IExecutionMethodCall} which provides the call stack.
     * @param sb The {@link StringBuilder} to append to.
     */
    protected void appendMethodReturns(int level, IExecutionMethodCall node, StringBuilder sb) {
        ImmutableList<IExecutionBaseMethodReturn<?>> methodReturns = node.getMethodReturns();
        if (methodReturns != null) {
            for (IExecutionBaseMethodReturn<?> methodReturn : methodReturns) {
                Map<String, String> attributeValues = new LinkedHashMap<>();
                attributeValues.put(ATTRIBUTE_PATH_IN_TREE, computePath(methodReturn));
                appendEmptyTag(level, TAG_METHOD_RETURN_ENTRY, attributeValues, sb);
            }
        }
    }

    /**
     * Appends the completed block entries to the given {@link StringBuilder}.
     *
     * @param level The level of the children.
     * @param node The {@link IExecutionNode} which provides the block entries.
     * @param sb The {@link StringBuilder} to append to.
     * @throws ProofInputException Occurred Exception
     */
    protected void appendCompletedBlocks(int level, IExecutionNode<?> node, StringBuilder sb)
            throws ProofInputException {
        ImmutableList<IExecutionBlockStartNode<?>> completedBlocks = node.getCompletedBlocks();
        if (completedBlocks != null) {
            for (IExecutionBlockStartNode<?> completedBlock : completedBlocks) {
                Map<String, String> attributeValues = new LinkedHashMap<>();
                attributeValues.put(ATTRIBUTE_PATH_IN_TREE, computePath(completedBlock));
                attributeValues.put(ATTRIBUTE_CONDITION_STRING,
                    node.getFormatedBlockCompletionCondition(completedBlock));
                appendEmptyTag(level, TAG_COMPLETED_BLOCK_ENTRY, attributeValues, sb);
            }
        }
    }

    /**
     * Appends the block completion entries to the given {@link StringBuilder}.
     *
     * @param level The level of the children.
     * @param node The {@link IExecutionBlockStartNode} which provides the completed blocks.
     * @param sb The {@link StringBuilder} to append to.
     */
    protected void appendBlockCompletions(int level, IExecutionBlockStartNode<?> node,
            StringBuilder sb) {
        ImmutableList<IExecutionNode<?>> blockCompletions = node.getBlockCompletions();
        if (blockCompletions != null) {
            for (IExecutionNode<?> blockCompletion : blockCompletions) {
                Map<String, String> attributeValues = new LinkedHashMap<>();
                attributeValues.put(ATTRIBUTE_PATH_IN_TREE, computePath(blockCompletion));
                appendEmptyTag(level, TAG_BLOCK_COMPLETION_ENTRY, attributeValues, sb);
            }
        }
    }

    /**
     * Computes the path from the root of the symbolic execution tree to the given
     * {@link IExecutionNode}.
     *
     * @param node The {@link IExecutionNode} to compute path to.
     * @return The computed path.
     */
    protected String computePath(IExecutionNode<?> node) {
        StringBuilder sb = new StringBuilder();
        boolean afterFirst = false;
        while (node != null) {
            IExecutionNode<?> parent = node.getParent();
            if (parent != null) {
                if (afterFirst) {
                    sb.insert(0, PATH_SEPARATOR);
                } else {
                    afterFirst = true;
                }
                int index = ArrayUtil.indexOf(parent.getChildren(), node);
                assert index >= 0 : "Node \"" + node + "\" is not contained in parents children \""
                    + Arrays.toString(parent.getChildren()) + "\".";
                sb.insert(0, index);
            } else {
                sb.insert(0, PATH_SEPARATOR);
            }
            node = parent;
        }
        return sb.toString();
    }
}
