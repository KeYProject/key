/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.key.ui.test.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Iterator;
import java.util.List;

import de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcProofContainer;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcSpecification;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer;
import de.hentschel.visualdbc.dbcmodel.DbCAxiomContract;
import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcConstructor;
import de.hentschel.visualdbc.dbcmodel.DbcEnum;
import de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral;
import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcInvariant;
import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcPackage;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcProofStatus;
import de.hentschel.visualdbc.dbcmodel.DbcProperty;
import de.hentschel.visualdbc.dbcmodel.DbcVisibility;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

/**
 * Provides static methods which makes testing easier.
 * @author Martin Hentschel
 */
public final class TestKeYUIUtil {
   /**
    * Forbid instances.
    */
   private TestKeYUIUtil() {
   }
   
   /**
    * Compares the given {@link DbcModel}.
    * @param expected The expected object.
    * @param current The current object.
    */
   public static void compareModels(DbcModel expected, DbcModel current) {
      compareContainer(expected, current, true);
      compareProperties(expected.getConnectionSettings(), current.getConnectionSettings());
      assertEquals(expected.getDriverId(), current.getDriverId());
      compareProofObligations(expected.getProofObligations(), current.getProofObligations());
   }

   /**
    * Compares the given {@link List} of {@link DbcProof}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareProofs(List<DbcProof> expected, List<DbcProof> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<DbcProof>() {
         @Override
         public void compare(DbcProof expected, DbcProof current) {
            compareProof(expected, current, compareReferences);
         }
      });
   }

   /**
    * Compares the given {@link DbcProof}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareProof(DbcProof expected, DbcProof current, final boolean compareReferences) {
      assertEquals(expected.getObligation(), current.getObligation());
      if (compareReferences) {
         compareReferences(expected.getProofReferences(), current.getProofReferences(), compareReferences);
      }
      compareStatus(expected.getStatus(), current.getStatus());
      compareProvable(expected.getTarget(), current.getTarget(), compareReferences);
   }

   /**
    * Compares the given {@link IDbCProvable}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareProvable(IDbCProvable expected, IDbCProvable current, boolean compareReferences) {
      if (expected instanceof DbcConstructor) {
         assertTrue(current instanceof DbcConstructor);
         compareConstructor((DbcConstructor)expected, (DbcConstructor)current, compareReferences);
      }
      else if (expected instanceof DbcMethod) {
         assertTrue(current instanceof DbcMethod);
         compareMethod((DbcMethod)expected, (DbcMethod)current, compareReferences);
      }
      else if (expected instanceof DbcInterface) {
         assertTrue(current instanceof DbcInterface);
         compareInterface((DbcInterface)expected, (DbcInterface)current, compareReferences);
      }
      else if (expected instanceof DbcClass) {
         assertTrue(current instanceof DbcClass);
         compareClass((DbcClass)expected, (DbcClass)current, compareReferences);
      }
      else if (expected instanceof DbcEnum) {
         assertTrue(current instanceof DbcEnum);
         compareEnum((DbcEnum)expected, (DbcEnum)current, compareReferences);
      }
      else if (expected instanceof DbCAxiomContract) {
         assertTrue(current instanceof DbCAxiomContract);
         compareAxiomContract((DbCAxiomContract)expected, (DbCAxiomContract)current, compareReferences);
      }
      else if (expected instanceof DbcOperationContract) {
         assertTrue(current instanceof DbcOperationContract);
         compareOperationContract((DbcOperationContract)expected, (DbcOperationContract)current);
      }
      else {
         fail("Unsupported provable: " + expected);
      }
   }

   /**
    * Compares the given {@link DbcProofStatus}.
    * @param expected The expected object.
    * @param current The current object.
    */
   public static void compareStatus(DbcProofStatus expected, DbcProofStatus current) {
      assertEquals(expected, current);
   }

   /**
    * Compares the given {@link List} of {@link DbcPackage}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void comparePackages(List<DbcPackage> expected, List<DbcPackage> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<DbcPackage>() {
         @Override
         public void compare(DbcPackage expected, DbcPackage current) {
            comparePackage(expected, current, compareReferences);
         }
      });
   }

   /**
    * Compares the given {@link DbcPackage}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void comparePackage(DbcPackage expected, DbcPackage current, boolean compareReferences) {
      compareContainer(expected, current, compareReferences);
      assertEquals(expected.getName(), current.getName());
   }

   /**
    * Compares the given {@link AbstractDbCContainer} ignoring the concrete type.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   protected static void compareContainer(AbstractDbCContainer expected, AbstractDbCContainer current, boolean compareReferences) {
      compareTypeContainer(expected, current, compareReferences);
      comparePackages(expected.getPackages(), current.getPackages(), compareReferences);
   }

   /**
    * Compares the given {@link AbstractDbcTypeContainer} ignoring the concrete type.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   protected static void compareTypeContainer(AbstractDbcTypeContainer expected, AbstractDbcTypeContainer current, boolean compareReferences) {
      compareProofContainer(expected, current, compareReferences);
      compareTypes(expected.getTypes(), current.getTypes(), compareReferences);
   }

   /**
    * Compares the given {@link AbstractDbcProofContainer} ignoring the concrete type.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   protected static void compareProofContainer(AbstractDbcProofContainer expected, AbstractDbcProofContainer current, boolean compareReferences) {
      compareProofs(expected.getProofs(), current.getProofs(), compareReferences);
   }

   /**
    * Compares the given {@link List} of {@link AbstractDbcType}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareTypes(List<AbstractDbcType> expected, List<AbstractDbcType> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<AbstractDbcType>() {
         @Override
         public void compare(AbstractDbcType expected, AbstractDbcType current) {
            if (expected instanceof DbcInterface) {
               assertTrue(current instanceof DbcInterface);
               compareInterface((DbcInterface)expected, (DbcInterface)current, compareReferences);
            }
            else if (expected instanceof DbcClass) {
               assertTrue(current instanceof DbcClass);
               compareClass((DbcClass)expected, (DbcClass)current, compareReferences);
            }
            else if (expected instanceof DbcEnum) {
               assertTrue(current instanceof DbcEnum);
               compareEnum((DbcEnum)expected, (DbcEnum)current, compareReferences);
            }
            else {
               fail("Unsupported type: " + expected);
            }
         }
      });
   }

   /**
    * Compares the given {@link List} of {@link DbcInterface}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareInterfaces(List<DbcInterface> expected, List<DbcInterface> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<DbcInterface>() {
         @Override
         public void compare(DbcInterface expected, DbcInterface current) {
            compareInterface(expected, current, compareReferences);
         }
      });
   }

   /**
    * Compares the given {@link DbcInterface}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareInterface(DbcInterface expected, DbcInterface current, boolean compareReferences) {
      compareType(expected, current, compareReferences);
      compareAttributes(expected.getAttributes(), current.getAttributes());
      compareInterfaces(expected.getExtends(), current.getExtends(), compareReferences);
      compareMethods(expected.getMethods(), current.getMethods(), compareReferences);
      compareProofObligations(expected.getProofObligations(), current.getProofObligations());
   }

   /**
    * Compares the given {@link List} of {@link DbcMethod}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareMethods(List<DbcMethod> expected, List<DbcMethod> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<DbcMethod>() {
         @Override
         public void compare(DbcMethod expected, DbcMethod current) {
            compareMethod(expected, current, compareReferences);
         }
      });
   }

   /**
    * Compares the given {@link DbcMethod}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareMethod(DbcMethod expected, DbcMethod current, boolean compareReferences) {
      compareOperation(expected, current, compareReferences);
      assertEquals(expected.isAbstract(), current.isAbstract());
      assertEquals(expected.isFinal(), current.isFinal());
      assertEquals(expected.getReturnType(), current.getReturnType());
   }

   /**
    * Compares the given {@link AbstractDbcOperation} ignoring the concrete type.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   protected static void compareOperation(AbstractDbcOperation expected, AbstractDbcOperation current, boolean compareReferences) {
      assertEquals(expected.isStatic(), current.isStatic());
      compareOperationContracts(expected.getOperationContracts(), current.getOperationContracts());
      compareProofObligations(expected.getProofObligations(), current.getProofObligations());
      compareProofs(expected.getProofs(), current.getProofs(), compareReferences);
      assertEquals(expected.getSignature(), current.getSignature());
      compareVisibility(expected.getVisibility(), current.getVisibility());
   }

   /**
    * Compares the given {@link List} of {@link DbcOperationContract}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareOperationContracts(List<DbcOperationContract> expected, List<DbcOperationContract> current) {
      compareLists(expected, current, new IListElementComperator<DbcOperationContract>() {
         @Override
         public void compare(DbcOperationContract expected, DbcOperationContract current) {
            compareOperationContract(expected, current);
         }
      });
   }

   /**
    * Compares the given {@link DbcOperationContract}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareOperationContract(DbcOperationContract expected, DbcOperationContract current) {
      compareSpecification(expected, current);
      assertEquals(expected.getModifies(), current.getModifies());
      assertEquals(expected.getPost(), current.getPost());
      assertEquals(expected.getPre(), current.getPre());
      compareProofObligations(expected.getProofObligations(), current.getProofObligations());
   }

   /**
    * Compares the given {@link List} of {@link DbcAttribute}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareAttributes(List<DbcAttribute> expected, List<DbcAttribute> current) {
      compareLists(expected, current, new IListElementComperator<DbcAttribute>() {
         @Override
         public void compare(DbcAttribute expected, DbcAttribute current) {
            compareAttribute(expected, current);
         }
      });
   }

   /**
    * Compares the given {@link DbcAttribute}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareAttribute(DbcAttribute expected, DbcAttribute current) {
      assertEquals(expected.isFinal(), current.isFinal());
      assertEquals(expected.isStatic(), current.isStatic());
      assertEquals(expected.getName(), current.getName());
      assertEquals(expected.getType(), current.getType());
      compareVisibility(expected.getVisibility(), current.getVisibility());
   }

   /**
    * Compares the given {@link List} of {@link DbcClass}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareClasses(List<DbcClass> expected, List<DbcClass> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<DbcClass>() {
         @Override
         public void compare(DbcClass expected, DbcClass current) {
            compareClass(expected, current, compareReferences);
         }
      });
   }

   /**
    * Compares the given {@link DbcClass}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareClass(DbcClass expected, DbcClass current, boolean compareReferences) {
      compareType(expected, current, compareReferences);
      assertEquals(expected.isAbstract(), current.isAbstract());
      assertEquals(expected.isAnonymous(), current.isAnonymous());
      assertEquals(expected.isFinal(), current.isFinal());
      assertEquals(expected.isStatic(), current.isStatic());
      compareAttributes(expected.getAttributes(), current.getAttributes());
      compareConstructors(expected.getConstructors(), current.getConstructors(), compareReferences);
      compareClasses(expected.getExtends(), current.getExtends(), compareReferences);
      compareInterfaces(expected.getImplements(), current.getImplements(), compareReferences);
      compareMethods(expected.getMethods(), current.getMethods(), compareReferences);
      compareProofObligations(expected.getProofObligations(), current.getProofObligations());
   }

   /**
    * Compares the given {@link List} of {@link DbcConstructor}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareConstructors(List<DbcConstructor> expected, List<DbcConstructor> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<DbcConstructor>() {
         @Override
         public void compare(DbcConstructor expected, DbcConstructor current) {
            compareConstructor(expected, current, compareReferences);
         }
      });
   }

   /**
    * Compares the given {@link DbcConstructor}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareConstructor(DbcConstructor expected, DbcConstructor current, boolean compareReferences) {
      compareOperation(expected, current, compareReferences);
   }

   /**
    * Compares the given {@link DbcEnum}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareEnum(DbcEnum expected, DbcEnum current, boolean compareReferences) {
      compareType(expected, current, compareReferences);
      assertEquals(expected.isStatic(), current.isStatic());
      compareAttributes(expected.getAttributes(), current.getAttributes());
      compareConstructors(expected.getConstructors(), current.getConstructors(), compareReferences);
      compareInterfaces(expected.getImplements(), current.getImplements(), compareReferences);
      compareLiterals(expected.getLiterals(), current.getLiterals());
      compareMethods(expected.getMethods(), current.getMethods(), compareReferences);
      compareProofObligations(expected.getProofObligations(), current.getProofObligations());
   }

   /**
    * Compares the given {@link List} of {@link DbcEnumLiteral}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareLiterals(List<DbcEnumLiteral> expected, List<DbcEnumLiteral> current) {
      compareLists(expected, current, new IListElementComperator<DbcEnumLiteral>() {
         @Override
         public void compare(DbcEnumLiteral expected, DbcEnumLiteral current) {
            compareLiteral(expected, current);
         }
      });
   }

   /**
    * Compares the given {@link DbcEnumLiteral}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareLiteral(DbcEnumLiteral expected, DbcEnumLiteral current) {
      assertEquals(expected.getName(), current.getName());
   }

   /**
    * Compares the given {@link AbstractDbcType} ignoring the concrete type.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   protected static void compareType(AbstractDbcType expected, AbstractDbcType current, boolean compareReferences) {
      compareTypeContainer(expected, current, compareReferences);
      assertEquals(expected.isStatic(), current.isStatic());
      compareAxioms(expected.getAxioms(), current.getAxioms(), compareReferences);
      compareInvariants(expected.getInvariants(), current.getInvariants(), compareReferences);
      if (!(expected instanceof DbcClass) || !((DbcClass)expected).isAnonymous()) {
         assertEquals(expected.getName(), current.getName()); // Do not compare names of anonymous classes because it's name contains a random number
      }
      compareVisibility(expected.getVisibility(), current.getVisibility());
   }

   /**
    * Compares the given {@link DbcVisibility}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareVisibility(DbcVisibility expected, DbcVisibility current) {
      assertEquals(expected, current);
   }

   /**
    * Compares the given {@link List} of {@link DbcInvariant}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareInvariants(List<DbcInvariant> expected, List<DbcInvariant> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<DbcInvariant>() {
         @Override
         public void compare(DbcInvariant expected, DbcInvariant current) {
            compareInvariant(expected, current, compareReferences);
         }
      });
   }

   /**
    * Compares the given {@link DbcInvariant}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareInvariant(DbcInvariant expected, DbcInvariant current, boolean compareReferences) {
      compareSpecification(expected, current);
      assertEquals(expected.getCondition(), current.getCondition());
   }

   /**
    * Compares the given {@link List} of {@link DbcAxiom}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareAxioms(List<DbcAxiom> expected, List<DbcAxiom> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<DbcAxiom>() {
         @Override
         public void compare(DbcAxiom expected, DbcAxiom current) {
            compareAxiom(expected, current, compareReferences);
         }
      });
   }

   /**
    * Compares the given {@link DbcAxiom}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareAxiom(DbcAxiom expected, DbcAxiom current, boolean compareReferences) {
      compareSpecification(expected, current);
      compareAxiomContracts(expected.getAxiomContracts(), current.getAxiomContracts(), compareReferences);
      assertEquals(expected.getDefinition(), current.getDefinition());
   }

   /**
    * Compares the given {@link List} of {@link DbCAxiomContract}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareAxiomContracts(List<DbCAxiomContract> expected, List<DbCAxiomContract> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<DbCAxiomContract>() {
         @Override
         public void compare(DbCAxiomContract expected, DbCAxiomContract current) {
            compareAxiomContract(expected, current, compareReferences);
         }
      });
   }

   /**
    * Compares the given {@link DbCAxiomContract}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareAxiomContract(DbCAxiomContract expected, DbCAxiomContract current, boolean compareReferences) {
      compareSpecification(expected, current);
      assertEquals(expected.getDep(), current.getDep());
      assertEquals(expected.getPre(), current.getPre());
      compareProofObligations(expected.getProofObligations(), current.getProofObligations());
   }

   /**
    * Compares the given {@link List} of {@link DbcProofReference}s.
    * @param expected The expected objects.
    * @param current The current objects.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareReferences(List<DbcProofReference> expected, List<DbcProofReference> current, final boolean compareReferences) {
      compareLists(expected, current, new IListElementComperator<DbcProofReference>() {
         @Override
         public void compare(DbcProofReference expected, DbcProofReference current) {
            compareReference(expected, current, compareReferences);
         }
      });
   }

   /**
    * Compares the given {@link DbcProofReference}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareReference(DbcProofReference expected, DbcProofReference current, boolean compareReferences) {
      assertEquals(expected.getKind(), current.getKind());
      compareProof(expected.getSource(), current.getSource(), false);
      compareReferencable(expected.getTarget(), current.getTarget(), false);
   }

   /**
    * Compares the given {@link IDbCProofReferencable}.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   public static void compareReferencable(IDbCProofReferencable expected, IDbCProofReferencable current, boolean compareReferences) {
      if (expected instanceof DbcAttribute) {
         assertTrue(current instanceof DbcAttribute);
         compareAttribute((DbcAttribute)expected, (DbcAttribute)current);
      }
      else if (expected instanceof DbcAxiom) {
         assertTrue(current instanceof DbcAxiom);
         compareAxiom((DbcAxiom)expected, (DbcAxiom)current, compareReferences);
      }
      else if (expected instanceof DbcEnumLiteral) {
         assertTrue(current instanceof DbcEnumLiteral);
         compareLiteral((DbcEnumLiteral)expected, (DbcEnumLiteral)current);
      }
      else if (expected instanceof DbcInvariant) {
         assertTrue(current instanceof DbcInvariant);
         compareInvariant((DbcInvariant)expected, (DbcInvariant)current, compareReferences);
      }
      else if (expected instanceof IDbCProvable) {
         assertTrue(current instanceof IDbCProvable);
         compareProvable((IDbCProvable)expected, (IDbCProvable)current, compareReferences);
      }
      else {
         fail("Unsupported Referencable: " + expected);
      }
   }

   /**
    * Compares the given {@link AbstractDbcSpecification} ignoring the concrete type.
    * @param expected The expected object.
    * @param current The current object.
    * @param {@code true} compare {@link DbcProofReference}s, {@code false} ignore {@link DbcProofReference}s.
    */
   protected static void compareSpecification(AbstractDbcSpecification expected, AbstractDbcSpecification current) {
      assertEquals(expected.getName(), current.getName());
   }
   
   /**
    * Compares the given {@link List} of {@link DbcProofObligation}s.
    * @param expected The expected objects.
    * @param current The current objects.
    */
   public static void compareProofObligations(List<DbcProofObligation> expected, List<DbcProofObligation> current) {
      compareLists(expected, current, new IListElementComperator<DbcProofObligation>() {
         @Override
         public void compare(DbcProofObligation expected, DbcProofObligation current) {
            compareProofObligation(expected, current);
         }
      });
   }

   /**
    * Compares the given {@link DbcProofObligation}.
    * @param expected The expected object.
    * @param current The current object.
    */
   public static void compareProofObligation(DbcProofObligation expected, DbcProofObligation current) {
      assertEquals(expected.getObligation(), current.getObligation());
   }

   /**
    * Compares the given {@link List} of {@link DbcProperty}s.
    * @param expected The expected objects.
    * @param current The current objects.
    */
   public static void compareProperties(List<DbcProperty> expected, List<DbcProperty> current) {
      compareLists(expected, current, new IListElementComperator<DbcProperty>() {
         @Override
         public void compare(DbcProperty expected, DbcProperty current) {
            compareProperty(expected, current);
         }
      });
   }

   /**
    * Compares the given {@link DbcProperty}.
    * @param expected The expected object.
    * @param current The current object.
    */
   public static void compareProperty(DbcProperty expected, DbcProperty current) {
      assertEquals(expected.getKey(), current.getKey());
      assertEquals(expected.getValue(), current.getValue());
   }
   
   /**
    * Compares the elements of the given {@link List}.
    * @param expected The expected elements.
    * @param current The current elements.
    * @param comperator The {@link IListElementComperator} to use.
    */
   public static <T> void compareLists(List<T> expected, List<T> current, IListElementComperator<T> comperator) {
      assertEquals(expected.size(), current.size());
      Iterator<T> expectedIter = expected.iterator();
      Iterator<T> currentIter = current.iterator();
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         comperator.compare(expectedIter.next(), currentIter.next());
      }
      assertFalse(expectedIter.hasNext());
      assertFalse(currentIter.hasNext());
   }
   
   /**
    * Utility class used by {@link TestKeYUIUtil#compareLists(List, List, IListElementComperator)}
    * to compare the elements of two {@link List}s.
    * @author Martin Hentschel
    */
   public static interface IListElementComperator<T> {
      public void compare(T first, T second);
   }
}