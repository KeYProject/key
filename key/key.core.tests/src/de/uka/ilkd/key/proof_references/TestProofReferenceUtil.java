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

package de.uka.ilkd.key.proof_references;

import java.io.File;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.proof_references.analyst.ContractProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.analyst.IProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.analyst.MethodBodyExpandProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

/**
 * Tests for {@link ProofReferenceUtil}.
 * @author Martin Hentschel
 */
public class TestProofReferenceUtil extends AbstractProofReferenceTestCase {
   /**
    * Tests {@link ProofReferenceUtil#computeProofReferences(Proof, ImmutableList)} and
    * {@link ProofReferenceUtil#computeProofReferences(Node, ImmutableList)}.
    */
   public void testReferenceComputation_ExpandAndContract() throws Exception {
      doAPITest(keyRepDirectory, 
                "examples/_testcase/proofReferences/UseOperationContractTest/UseOperationContractTest.java", 
                "UseOperationContractTest", 
                "main", 
                true,
                ImmutableSLList.<IProofReferencesAnalyst>nil().append(new MethodBodyExpandProofReferencesAnalyst(), new ContractProofReferencesAnalyst()),
                new ExpectedProofReferences(IProofReference.INLINE_METHOD, "UseOperationContractTest::main"), 
                new ExpectedProofReferences(IProofReference.USE_CONTRACT, "pre: {heap=java.lang.Object::<inv>(heap,self)}; mby: null; post: {heap=and(and(equals(result,Z(2(4(#)))),java.lang.Object::<inv>(heap,self)),equals(exc,null))}; mods: {heap=allLocs, savedHeap=null}; hasMod: {heap=true, savedHeap=true}; termination: diamond; transaction: false"));
   }
   
   /**
    * Tests {@link ProofReferenceUtil#computeProofReferences(Proof, ImmutableList)} and
    * {@link ProofReferenceUtil#computeProofReferences(Node, ImmutableList)}.
    */
   public void testReferenceComputation_NoAnalysts() throws Exception {
      doAPITest(keyRepDirectory, 
                "examples/_testcase/proofReferences/MethodBodyExpand/MethodBodyExpand.java", 
                "MethodBodyExpand", 
                "main", 
                false,
                ImmutableSLList.<IProofReferencesAnalyst>nil());
   }
   
   /**
    * Tests {@link ProofReferenceUtil#computeProofReferences(Proof, ImmutableList)} and
    * {@link ProofReferenceUtil#computeProofReferences(Node, ImmutableList)}.
    */
   public void testReferenceComputation_ContractOnly() throws Exception {
      doAPITest(keyRepDirectory, 
                "examples/_testcase/proofReferences/MethodBodyExpand/MethodBodyExpand.java", 
                "MethodBodyExpand", 
                "main", 
                false,
                ImmutableSLList.<IProofReferencesAnalyst>nil().append(new ContractProofReferencesAnalyst()));
   }
   
   /**
    * Tests {@link ProofReferenceUtil#computeProofReferences(Proof, ImmutableList)} and
    * {@link ProofReferenceUtil#computeProofReferences(Node, ImmutableList)}.
    */
   public void testReferenceComputation_ExpandOnly() throws Exception {
      doAPITest(keyRepDirectory, 
                "examples/_testcase/proofReferences/MethodBodyExpand/MethodBodyExpand.java", 
                "MethodBodyExpand", 
                "main", 
                false,
                ImmutableSLList.<IProofReferencesAnalyst>nil().append(new MethodBodyExpandProofReferencesAnalyst()),
                new ExpectedProofReferences(IProofReference.INLINE_METHOD, "MethodBodyExpand::main"), 
                new ExpectedProofReferences(IProofReference.INLINE_METHOD, "MethodBodyExpand::magic42"));
   }
   
   /**
    * Tests {@link ProofReferenceUtil#computeProofReferences(Proof)} and
    * {@link ProofReferenceUtil#computeProofReferences(Node)}.
    */
   public void testReferenceComputation_DefaultAnalysts() throws Exception {
      doAPITest(keyRepDirectory, 
                "examples/_testcase/proofReferences/MethodBodyExpand/MethodBodyExpand.java", 
                "MethodBodyExpand", 
                "main",
                false,
                null,
                new ExpectedProofReferences(IProofReference.USE_AXIOM, "equiv(java.lang.Object::<inv>(heap,self),true)"), 
                new ExpectedProofReferences(IProofReference.INLINE_METHOD, "MethodBodyExpand::main"), 
                new ExpectedProofReferences(IProofReference.CALL_METHOD, "MethodBodyExpand::magic42"), 
                new ExpectedProofReferences(IProofReference.INLINE_METHOD, "MethodBodyExpand::magic42"));
   }
   
   /**
    * Executes the test steps of test methods. 
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The name of the type which contains the method.
    * @param methodFullName The method name to search.
    * @param useContracts Use method contracts or inline method bodies instead?
    * @param analysts The {@link IProofReferencesAnalyst} to use.
    * @param expectedReferences The expected proof references.
    * @throws Exception Occurred Exception.
    */
   protected void doAPITest(File baseDir, 
                            String javaPathInBaseDir, 
                            String containerTypeName, 
                            String methodFullName,
                            boolean useContracts,
                            final ImmutableList<IProofReferencesAnalyst> analysts,
                            final ExpectedProofReferences... expectedReferences) throws Exception {
      IProofTester tester = new IProofTester() {
         @Override
         public void doTest(KeYEnvironment<?> environment, Proof proof) throws Exception {
            // Extract and assert proof references
            final LinkedHashSet<IProofReference<?>> references = analysts != null ? 
                                                                 ProofReferenceUtil.computeProofReferences(proof, analysts) : 
                                                                 ProofReferenceUtil.computeProofReferences(proof);
            assertReferences(references, expectedReferences);
            // Test references of each node individually
            proof.breadthFirstSearch(proof.root(), new ProofVisitor() {
               @Override
               public void visit(Proof proof, Node visitedNode) {
                  LinkedHashSet<IProofReference<?>> expectedNodeRefs = findReferences(references, visitedNode);
                  LinkedHashSet<IProofReference<?>> currentNodeRefs = analysts != null ? 
                                                                      ProofReferenceUtil.computeProofReferences(visitedNode, proof.getServices(), analysts) : 
                                                                      ProofReferenceUtil.computeProofReferences(visitedNode, proof.getServices());
                  assertReferences(expectedNodeRefs, currentNodeRefs);
               }
            });
         }
      };
      doProofMethodTest(baseDir, javaPathInBaseDir, containerTypeName, methodFullName, useContracts, tester);
   }
}