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

package de.hentschel.visualdbc.datasource.test.dummyModel;

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConnectionSetting;
import de.hentschel.visualdbc.datasource.model.IDSConstructor;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.IDSPackage;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSDriver;
import de.hentschel.visualdbc.datasource.model.memory.MemoryAttribute;
import de.hentschel.visualdbc.datasource.model.memory.MemoryClass;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnection;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConstructor;
import de.hentschel.visualdbc.datasource.model.memory.MemoryEnum;
import de.hentschel.visualdbc.datasource.model.memory.MemoryEnumLiteral;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInterface;
import de.hentschel.visualdbc.datasource.model.memory.MemoryMethod;
import de.hentschel.visualdbc.datasource.model.memory.MemoryPackage;

/**
 * Creates an {@link IDSConnection} that represents always the dummy model
 * that is used in tests.
 * @author Martin Hentschel
 */
public class DummyModelDriver extends AbstractDSDriver {
   /**
    * The ID of this driver.
    */
   public static final String ID = "de.hentschel.visualdbc.generation.test.dummyModel";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public int getPriority() {
      return Integer.MIN_VALUE;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getId() {
      return ID;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Dummy Model";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSConnectionSetting> getConnectionSettings() {
      return new LinkedList<IDSConnectionSetting>();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSConnection createConnection() throws DSException {
      // Create connection
      MemoryConnection connection = new MemoryConnection(this);
      // Add root packages
      MemoryPackage rootEmptyPackage = createPackage("rootEmptyPackage");
      connection.addPackage(rootEmptyPackage);

      MemoryEnum rootWithChildren29e1 = createEnum("rootWithChildren29e1", true, DSVisibility.PRIVATE);
      MemoryEnum rootWithChildren29e2 = createEnum("rootWithChildren29e2", true, DSVisibility.PRIVATE);
      MemoryPackage rootWithChildren29 = createPackage("rootWithChildren.2.9", rootWithChildren29e1, rootWithChildren29e2);
      
      MemoryClass rootWithChildren28eC1 = createClass(false, false, "rootWithChildren28eC1", false, DSVisibility.DEFAULT);
      MemoryClass rootWithChildren28eC2 = createClass(false, false, "rootWithChildren28eC2", false, DSVisibility.DEFAULT);
      MemoryInterface rootWithChildren28eI1 = createInterface("rootWithChildren28eI1", true, DSVisibility.DEFAULT);
      MemoryInterface rootWithChildren28eI2 = createInterface("rootWithChildren28eI2", true, DSVisibility.DEFAULT);
      MemoryEnum rootWithChildren28eE1 = createEnum("rootWithChildren28eE1", true, DSVisibility.DEFAULT);
      MemoryEnum rootWithChildren28eE2 = createEnum("rootWithChildren28eE2", true, DSVisibility.DEFAULT);
      MemoryEnum rootWithChildren28e = createEnum("rootWithChildren28e", true, DSVisibility.PRIVATE, rootWithChildren28eC1, rootWithChildren28eC2, rootWithChildren28eI1, rootWithChildren28eI2, rootWithChildren28eE1, rootWithChildren28eE2);
      MemoryPackage rootWithChildren28 = createPackage("rootWithChildren.2.8", rootWithChildren28e);
 
      MemoryInterface rootWithChildren27i1 = createInterface("rootWithChildren27i1", true, DSVisibility.PRIVATE);
      MemoryInterface rootWithChildren27i2 = createInterface("rootWithChildren27i2", true, DSVisibility.PRIVATE);
      MemoryPackage rootWithChildren27 = createPackage("rootWithChildren.2.7", rootWithChildren27i1, rootWithChildren27i2);
      
      MemoryClass rootWithChildren26iC1 = createClass(false, false, "rootWithChildren26iC1", false, DSVisibility.DEFAULT);
      MemoryClass rootWithChildren26iC2 = createClass(false, false, "rootWithChildren26iC2", false, DSVisibility.DEFAULT);
      MemoryClass rootWithChildren26iC3 = createClass(false, false, "rootWithChildren26iC3", false, DSVisibility.DEFAULT);
      MemoryInterface rootWithChildren26iI1 = createInterface("rootWithChildren26iI1", true, DSVisibility.DEFAULT);
      MemoryInterface rootWithChildren26iI2 = createInterface("rootWithChildren26iI2", true, DSVisibility.DEFAULT);
      MemoryInterface rootWithChildren26iI3 = createInterface("rootWithChildren26iI3", true, DSVisibility.DEFAULT);
      MemoryEnum rootWithChildren26iE1 = createEnum("rootWithChildren26iE1", true, DSVisibility.DEFAULT);
      MemoryEnum rootWithChildren26iE2 = createEnum("rootWithChildren26iE2", true, DSVisibility.DEFAULT);
      MemoryEnum rootWithChildren26iE3 = createEnum("rootWithChildren26iE3", true, DSVisibility.DEFAULT);
      MemoryInterface rootWithChildren26i = createInterface("rootWithChildren26i", true, DSVisibility.PRIVATE, rootWithChildren26iC1, rootWithChildren26iC2, rootWithChildren26iC3, rootWithChildren26iE1, rootWithChildren26iE2, rootWithChildren26iE3, rootWithChildren26iI1, rootWithChildren26iI2, rootWithChildren26iI3);
      MemoryPackage rootWithChildren26 = createPackage("rootWithChildren.2.6", rootWithChildren26i);
      
      MemoryClass rootWithChildren25c1 = createClass(false, false, "rootWithChildren25c1", false, DSVisibility.PUBLIC);
      MemoryClass rootWithChildren25c2 = createClass(false, false, "rootWithChildren25c2", false, DSVisibility.PUBLIC);
      MemoryPackage rootWithChildren25 = createPackage("rootWithChildren.2.5", rootWithChildren25c1, rootWithChildren25c2);

      MemoryClass rootWithChildren24cC = createClass(false, false, "rootWithChildren24cC", false, DSVisibility.DEFAULT);
      MemoryInterface rootWithChildren24cI = createInterface("rootWithChildren24cI", true, DSVisibility.DEFAULT);
      MemoryEnum rootWithChildren24cE = createEnum("rootWithChildren24cE", true, DSVisibility.DEFAULT);
      MemoryClass rootWithChildren24c = createClass(false, false, "rootWithChildren24c", false, DSVisibility.PUBLIC, rootWithChildren24cE, rootWithChildren24cI, rootWithChildren24cC);
      MemoryPackage rootWithChildren24 = createPackage("rootWithChildren.2.4", rootWithChildren24c);
      
      MemoryPackage rootWithChildren231 = createPackage("rootWithChildren.2.3.1");
      MemoryClass rootWithChildren23c = createClass(false, false, "rootWithChildren23c", false, DSVisibility.PUBLIC);
      MemoryInterface rootWithChildren23i = createInterface("rootWithChildren23i", true, DSVisibility.PRIVATE);
      MemoryEnum rootWithChildren23e = createEnum("rootWithChildren23e", true, DSVisibility.PRIVATE);
      MemoryPackage rootWithChildren23 = createPackage("rootWithChildren.2.3", rootWithChildren231, rootWithChildren23c, rootWithChildren23e, rootWithChildren23i);
      MemoryPackage rootWithChildren22 = createPackage("rootWithChildren.2.2");
      MemoryPackage rootWithChildren21 = createPackage("rootWithChildren.2.1");
      MemoryPackage rootWithChildren2 = createPackage("rootWithChildren.2", rootWithChildren21, rootWithChildren22, rootWithChildren23, rootWithChildren24, rootWithChildren25, rootWithChildren26, rootWithChildren27, rootWithChildren28, rootWithChildren29);
      MemoryPackage rootWithChildren1 = createPackage("rootWithChildren.1");
      MemoryPackage rootWithChildren = createPackage("rootWithChildren", rootWithChildren1, rootWithChildren2);
      connection.addPackage(rootWithChildren);
      // Add root interfaces
      MemoryInterface riDefault = createInterface("riDefault", true, DSVisibility.DEFAULT);
      connection.addInterface(riDefault);
      MemoryInterface riPrivate = createInterface("riPrivate", false, DSVisibility.PRIVATE);
      connection.addInterface(riPrivate);
      MemoryInterface riProtected = createInterface("riProtected", true, DSVisibility.PROTECTED);
      connection.addInterface(riProtected);
      MemoryInterface riPublic = createInterface("riPublic", false, DSVisibility.PUBLIC);
      connection.addInterface(riPublic);
      
      MemoryClass riInnerTypesC = createClass(false, false, "riInnerTypesC", false, DSVisibility.DEFAULT);
      MemoryInterface riInnerTypesI = createInterface("riInnerTypesI", true, DSVisibility.DEFAULT);
      MemoryEnum riInnerTypesE = createEnum("riInnerTypesE", true, DSVisibility.DEFAULT);
      MemoryInterface riInnerTypes = createInterface("riInnerTypes", true, DSVisibility.PUBLIC, riInnerTypesC, riInnerTypesI, riInnerTypesE);
      connection.addInterface(riInnerTypes);

      MemoryAttribute riAttributesDefault = createAttribute(false, "riAttributesDefault", true, "int", DSVisibility.DEFAULT);
      MemoryAttribute riAttributesPrivate = createAttribute(false, "riAttributesPrivate", true, "java.lang.String", DSVisibility.PRIVATE);
      MemoryAttribute riAttributesProtected = createAttribute(false, "riAttributesProtected", true, "java.io.File[]", DSVisibility.PROTECTED);
      MemoryAttribute riAttributesPublic = createAttribute(false, "riAttributesPublic", true, "int[]", DSVisibility.PUBLIC);
      MemoryInterface riAttributes = createInterface("riAttributes", true, DSVisibility.DEFAULT, riAttributesDefault, riAttributesPrivate, riAttributesProtected, riAttributesPublic);
      connection.addInterface(riAttributes);

      MemoryMethod riMethodDefault = createMethod(false, true, "void", "riMethodDefault()", false, DSVisibility.DEFAULT);
      MemoryMethod riMethodPrivate = createMethod(true, false, "void", "riMethodDefault(x : String)", true, DSVisibility.PRIVATE);
      MemoryMethod ricMethodProtected = createMethod(true, false, "java.lang.String", "riMethodProtected(y : java.lang.String[])", true, DSVisibility.PROTECTED);
      MemoryMethod riMethodPublic = createMethod(false, true, "int[]", "riMethodPublic(x : double[])", false, DSVisibility.PUBLIC);
      MemoryInterface riMethods = createInterface("riMethods", true, DSVisibility.DEFAULT, riMethodDefault, riMethodPrivate, ricMethodProtected, riMethodPublic);
      connection.addInterface(riMethods);
      
      MemoryInterface riPackageExtendSource = createInterface("riPackageExtendSource", true, DSVisibility.DEFAULT);
      MemoryInterface riPackageExtendTargetSource = createInterface("riPackageExtendTargetSource", true, DSVisibility.DEFAULT);
      MemoryInterface riPackageExtendTargetTarget = createInterface("riPackageExtendTargetTarget", true, DSVisibility.DEFAULT);
      MemoryInterface riPackageExtendTarget = createInterface("riPackageExtendTarget", true, DSVisibility.DEFAULT, riPackageExtendTargetSource, riPackageExtendTargetTarget);
      MemoryPackage extendsIPackage = createPackage("extendsPackage1", riPackageExtendSource, riPackageExtendTarget);
      connection.addPackage(extendsIPackage);
      MemoryInterface riExtendSource1 = createInterface("riExtendSource1", true, DSVisibility.DEFAULT);
      connection.addInterface(riExtendSource1);
      MemoryInterface riExtendTarget = createInterface("riExtendTarget", true, DSVisibility.DEFAULT);
      connection.addInterface(riExtendTarget);
      MemoryInterface riExtendSource2 = createInterface("riExtendSource2", true, DSVisibility.DEFAULT);
      connection.addInterface(riExtendSource2);
      riExtendSource1.getExtends().add(riExtendTarget);
      riExtendSource2.getExtends().add(riExtendTarget);
      riExtendSource2.getExtends().add(riPackageExtendTarget);
      riPackageExtendSource.getExtends().add(riPackageExtendTarget);
      riPackageExtendSource.getExtends().add(riExtendTarget);
      riPackageExtendTargetSource.getExtends().add(riPackageExtendTargetTarget);
      riPackageExtendTargetSource.getExtends().add(riExtendTarget);
      riPackageExtendTargetSource.getExtends().add(riPackageExtendTarget);
      // Add root classes
      MemoryClass rcDefault = createClass(false, false, "rcDefault", false, DSVisibility.DEFAULT);
      connection.addClass(rcDefault);
      MemoryClass rcPrivate = createClass(true, false, "rcPrivate", true, DSVisibility.PRIVATE);
      connection.addClass(rcPrivate);
      MemoryClass rcProtected = createClass(false, true, "rcProtected", false, DSVisibility.PROTECTED);
      connection.addClass(rcProtected);
      MemoryClass rcPublic = createClass(true, true, "rcPublic", true, DSVisibility.PUBLIC);
      connection.addClass(rcPublic);
      
      MemoryClass rcInnerTypesC = createClass(false, false, "rcInnerTypesC", false, DSVisibility.DEFAULT);
      MemoryInterface rcInnerTypesI = createInterface("rcInnerTypesI", true, DSVisibility.DEFAULT);
      MemoryEnum rcInnerTypesE = createEnum("rcInnerTypesE", true, DSVisibility.DEFAULT);
      MemoryClass rcInnerTypes = createClass(true, true, "rcInnerTypes", true, DSVisibility.PUBLIC, rcInnerTypesC, rcInnerTypesI, rcInnerTypesE);
      connection.addClass(rcInnerTypes);

      MemoryAttribute rcAttributesDefault = createAttribute(true, "rcAttributesDefault", true, "int", DSVisibility.DEFAULT);
      MemoryAttribute rcAttributesPrivate = createAttribute(false, "rcAttributesPrivate", false, "java.lang.String", DSVisibility.PRIVATE);
      MemoryAttribute rcAttributesProtected = createAttribute(true, "rcAttributesProtected", false, "java.io.File[]", DSVisibility.PROTECTED);
      MemoryAttribute rcAttributesPublic = createAttribute(false, "rcAttributesPublic", true, "int[]", DSVisibility.PUBLIC);
      MemoryClass rcAttributes = createClass(true, true, "rcAttributes", true, DSVisibility.PUBLIC, rcAttributesDefault, rcAttributesPrivate, rcAttributesProtected, rcAttributesPublic);
      connection.addClass(rcAttributes);

      MemoryMethod rcMethodDefault = createMethod(true, true, "void", "rcMethodDefault()", true, DSVisibility.DEFAULT);
      MemoryMethod rcMethodPrivate = createMethod(false, false, "void", "rcMethodDefault(x : String)", false, DSVisibility.PRIVATE);
      MemoryMethod rcMethodProtected = createMethod(false, true, "java.lang.String", "rcMethodProtected(y : java.lang.String[])", true, DSVisibility.PROTECTED);
      MemoryMethod rcMethodPublic = createMethod(true, false, "int[]", "rcMethodPublic(x : double[])", false, DSVisibility.PUBLIC);
      MemoryClass rcMethods = createClass(true, true, "rcMethods", true, DSVisibility.PUBLIC, rcMethodDefault, rcMethodPrivate, rcMethodProtected, rcMethodPublic);
      connection.addClass(rcMethods);

      MemoryConstructor rcConstructorDefault = createConstructor("rcConstructors()", true, DSVisibility.DEFAULT);
      MemoryConstructor rcConstructorPrivate = createConstructor("rcConstructors(x : int)", false, DSVisibility.PRIVATE);
      MemoryConstructor rcConstructorProtected = createConstructor("rcConstructorProtected(a : int[], b : int[])", true, DSVisibility.PROTECTED);
      MemoryConstructor rcConstructorPublic = createConstructor("rcConstructors(java.io.File)", false, DSVisibility.PUBLIC);
      MemoryClass rcConstructors = createClass(true, true, "rcConstructors", true, DSVisibility.PUBLIC, rcConstructorDefault, rcConstructorPrivate, rcConstructorProtected, rcConstructorPublic);
      connection.addClass(rcConstructors);

      MemoryClass rcPackageExtendSource = createClass(true, true, "rcPackageExtendSource", true, DSVisibility.PUBLIC);
      MemoryClass rcPackageExtendTargetSource = createClass(true, true, "rcPackageExtendTargetSource", true, DSVisibility.PUBLIC);
      MemoryClass rcPackageExtendTargetTarget = createClass(true, true, "rcPackageExtendTargetTarget", true, DSVisibility.PUBLIC);
      MemoryClass rcPackageExtendTarget = createClass(true, true, "rcPackageExtendTarget", true, DSVisibility.PUBLIC, rcPackageExtendTargetSource, rcPackageExtendTargetTarget);
      MemoryPackage extendsCPackage = createPackage("extendsPackage2", rcPackageExtendSource, rcPackageExtendTarget);
      connection.addPackage(extendsCPackage);
      MemoryClass rcExtendSource1 = createClass(true, true, "rcExtendSource1", true, DSVisibility.PUBLIC);
      connection.addClass(rcExtendSource1);
      MemoryClass rcExtendTarget = createClass(true, true, "rcExtendTarget", true, DSVisibility.PUBLIC);
      connection.addClass(rcExtendTarget);
      MemoryClass rcExtendSource2 = createClass(true, true, "rcExtendSource2", true, DSVisibility.PUBLIC);
      connection.addClass(rcExtendSource2);
      rcExtendSource1.getExtends().add(rcExtendTarget);
      rcExtendSource2.getExtends().add(rcExtendTarget);
      rcExtendSource2.getExtends().add(rcPackageExtendTarget);
      rcPackageExtendSource.getExtends().add(rcPackageExtendTarget);
      rcPackageExtendSource.getExtends().add(rcExtendTarget);
      rcPackageExtendTargetSource.getExtends().add(rcPackageExtendTargetTarget);
      rcPackageExtendTargetSource.getExtends().add(rcExtendTarget);
      rcPackageExtendTargetSource.getExtends().add(rcPackageExtendTarget);      

      rcExtendSource1.getImplements().add(riExtendTarget);
      rcExtendSource2.getImplements().add(riExtendTarget);
      rcExtendSource2.getImplements().add(riPackageExtendTarget);
      rcPackageExtendSource.getImplements().add(riPackageExtendTarget);
      rcPackageExtendSource.getImplements().add(riExtendTarget);
      rcPackageExtendTargetSource.getImplements().add(riPackageExtendTargetTarget);
      rcPackageExtendTargetSource.getImplements().add(riExtendTarget);
      rcPackageExtendTargetSource.getImplements().add(riPackageExtendTarget);
      // Add root enumerations
      MemoryEnum reDefault = createEnum("reDefault", true, DSVisibility.DEFAULT);
      connection.addEnum(reDefault);
      MemoryEnum rePrivate = createEnum("rePrivate", false, DSVisibility.PRIVATE);
      connection.addEnum(rePrivate);
      MemoryEnum reProtected = createEnum("reProtected", false, DSVisibility.PROTECTED);
      connection.addEnum(reProtected);
      MemoryEnum rePublic = createEnum("rePublic", true, DSVisibility.PUBLIC);
      connection.addEnum(rePublic);
      
      MemoryClass reInnerTypesC = createClass(false, false, "reInnerTypesC", false, DSVisibility.DEFAULT);
      MemoryInterface reInnerTypesI = createInterface("reInnerTypesI", true, DSVisibility.DEFAULT);
      MemoryEnum reInnerTypesE = createEnum("reInnerTypesE", true, DSVisibility.DEFAULT);
      MemoryEnum reInnerTypes = createEnum("reInnerTypes", true, DSVisibility.PUBLIC, reInnerTypesC, reInnerTypesI, reInnerTypesE);
      connection.addEnum(reInnerTypes);

      MemoryAttribute reAttributesDefault = createAttribute(false, "reAttributesDefault", true, "int", DSVisibility.DEFAULT);
      MemoryAttribute reAttributesPrivate = createAttribute(false, "reAttributesPrivate", true, "java.lang.String", DSVisibility.PRIVATE);
      MemoryAttribute reAttributesProtected = createAttribute(true, "reAttributesProtected", false, "java.io.File[]", DSVisibility.PROTECTED);
      MemoryAttribute reAttributesPublic = createAttribute(true, "reAttributesPublic", false, "int[]", DSVisibility.PUBLIC);
      MemoryEnum reAttributes = createEnum("reAttributes", false, DSVisibility.PRIVATE, reAttributesDefault, reAttributesPrivate, reAttributesProtected, reAttributesPublic);
      connection.addEnum(reAttributes);

      MemoryMethod reMethodDefault = createMethod(false, true, "void", "reMethodDefault()", true, DSVisibility.DEFAULT);
      MemoryMethod reMethodPrivate = createMethod(false, true, "void", "reMethodDefault(x : String)", false, DSVisibility.PRIVATE);
      MemoryMethod recMethodProtected = createMethod(true, false, "java.lang.String", "reMethodProtected(y : java.lang.String[])", false, DSVisibility.PROTECTED);
      MemoryMethod reMethodPublic = createMethod(true, false, "int[]", "reMethodPublic(x : double[])", true, DSVisibility.PUBLIC);
      MemoryEnum reMethods = createEnum("reMethods", false, DSVisibility.PRIVATE, reMethodDefault, reMethodPrivate, recMethodProtected, reMethodPublic);
      connection.addEnum(reMethods);

      MemoryConstructor reConstructorDefault = createConstructor("reConstructors()", true, DSVisibility.DEFAULT);
      MemoryConstructor reConstructorPrivate = createConstructor("reConstructors(x : int)", false, DSVisibility.PRIVATE);
      MemoryConstructor reConstructorProtected = createConstructor("reConstructorProtected(a : int[], b : int[])", true, DSVisibility.PROTECTED);
      MemoryConstructor reConstructorPublic = createConstructor("reConstructors(java.io.File)", false, DSVisibility.PUBLIC);
      MemoryEnum reConstructors = createEnum("reConstructors", false, DSVisibility.PRIVATE, reConstructorDefault, reConstructorPrivate, reConstructorProtected, reConstructorPublic);
      connection.addEnum(reConstructors);

      MemoryEnumLiteral reEnumLiteralsRed = createEnumLiteral("RED");
      MemoryEnumLiteral reEnumLiteralsGreen = createEnumLiteral("GREEN");
      MemoryEnumLiteral reEnumLiteralsBlue = createEnumLiteral("BLUE");
      MemoryEnum reEnumLiterals = createEnum("reEnumLiterals", false, DSVisibility.PRIVATE, reEnumLiteralsRed, reEnumLiteralsGreen, reEnumLiteralsBlue);
      connection.addEnum(reEnumLiterals);

      MemoryEnum rePackageExtendSource = createEnum("rePackageExtendSource", false, DSVisibility.PRIVATE);
      MemoryEnum rePackageExtendTargetSource = createEnum("rePackageExtendTargetSource", false, DSVisibility.PRIVATE);
      MemoryEnum rePackageExtendTargetTarget = createEnum("rePackageExtendTargetTarget", false, DSVisibility.PRIVATE);
      MemoryEnum rePackageExtendTarget = createEnum("rePackageExtendTarget", false, DSVisibility.PRIVATE, rePackageExtendTargetSource, rePackageExtendTargetTarget);
      MemoryPackage extendsEPackage = createPackage("extendsPackage3", rePackageExtendSource, rePackageExtendTarget);
      connection.addPackage(extendsEPackage);
      MemoryEnum reExtendSource1 = createEnum("reExtendSource1", false, DSVisibility.PRIVATE);
      connection.addEnum(reExtendSource1);
      MemoryEnum reExtendTarget = createEnum("reExtendTarget", false, DSVisibility.PRIVATE);
      connection.addEnum(reExtendTarget);
      MemoryEnum reExtendSource2 = createEnum("reExtendSource2", false, DSVisibility.PRIVATE);
      connection.addEnum(reExtendSource2);
      reExtendSource1.getImplements().add(riExtendTarget);
      reExtendSource2.getImplements().add(riExtendTarget);
      reExtendSource2.getImplements().add(riPackageExtendTarget);
      rePackageExtendSource.getImplements().add(riPackageExtendTarget);
      rePackageExtendSource.getImplements().add(riExtendTarget);
      rePackageExtendTargetSource.getImplements().add(riPackageExtendTargetTarget);
      rePackageExtendTargetSource.getImplements().add(riExtendTarget);
      rePackageExtendTargetSource.getImplements().add(riPackageExtendTarget);
      return connection;
   }
   
   /**
    * Creates a data source {@link IDSConstructor}.
    * @param signature The signature.
    * @param isStatic Is static?
    * @param visibility The visibility.
    * @return The created instance.
    */
   protected MemoryConstructor createConstructor(String signature, 
                                                 boolean isStatic, 
                                                 DSVisibility visibility) {
      MemoryConstructor instance = new MemoryConstructor();
      instance.setSignature(signature);
      instance.setStatic(isStatic);
      instance.setVisibility(visibility);
      return instance;
   }
   
   /**
    * Creates a data source {@link IDSMethod}.
    * @param isAbstract Is abstract?
    * @param isFinal Is final?
    * @param returnType The return type.
    * @param signature The signature.
    * @param isStatic Is static?
    * @param visibility The visibility.
    * @return The created instance.
    */
   protected MemoryMethod createMethod(boolean isAbstract, 
                                       boolean isFinal, 
                                       String returnType, 
                                       String signature, 
                                       boolean isStatic, 
                                       DSVisibility visibility) {
      MemoryMethod instance = new MemoryMethod();
      instance.setAbstract(isAbstract);
      instance.setFinal(isFinal);
      instance.setReturnType(returnType);
      instance.setSignature(signature);
      instance.setStatic(isStatic);
      instance.setVisibility(visibility);
      return instance;
   }
   
   /**
    * Creates a data source {@link IDSEnumLiteral}.
    * @param name The name.
    */
   protected MemoryEnumLiteral createEnumLiteral(String name) {
      MemoryEnumLiteral instance = new MemoryEnumLiteral();
      instance.setName(name);
      return instance;
   }
   
   /**
    * Creates a data source {@link IDSAttribute}.
    * @param isFinal Is final?
    * @param name The name.
    * @param isStatic Is static?
    * @param type The type.
    * @param visibility The visibility.
    * @return The created instance.
    */
   protected MemoryAttribute createAttribute(boolean isFinal, 
                                             String name, 
                                             boolean isStatic, 
                                             String type, 
                                             DSVisibility visibility) {
      MemoryAttribute instance = new MemoryAttribute();
      instance.setFinal(isFinal);
      instance.setName(name);
      instance.setStatic(isStatic);
      instance.setType(type);
      instance.setVisibility(visibility);
      return instance;
   }

   /**
    * Creates a data source {@link IDSPackage}.
    * @param name The name.
    * @param children The children.
    * @return The created instance.
    */
   protected MemoryPackage createPackage(String name, Object... children) {
      MemoryPackage instance = new MemoryPackage();
      instance.setName(name);
      for (Object child : children) {
         if (child instanceof MemoryPackage) {
            instance.addPackage((MemoryPackage)child);
         }
         else if (child instanceof MemoryClass) {
            instance.addClass((MemoryClass)child);
         }
         else if (child instanceof MemoryInterface) {
            instance.addInterface((MemoryInterface)child);
         }
         else if (child instanceof MemoryEnum) {
            instance.addEnum((MemoryEnum)child);
         }
         else {
            throw new IllegalArgumentException("Unsupported child \"" + child + "\".");
         }
      }
      return instance;
   }
   
   /**
    * Creates a data source {@link IDSClass}.
    * @param isAbstract The abstract flag.
    * @param isFinal The final flag.
    * @param name The name. 
    * @param isStatic The static flag.
    * @param visibility The visibility.
    * @param children The children.
    * @return The created instance.
    */
   protected MemoryClass createClass(boolean isAbstract, 
                                     boolean isFinal, 
                                     String name, 
                                     boolean isStatic, 
                                     DSVisibility visibility, 
                                     Object... children) {
      MemoryClass instance = new MemoryClass();
      instance.setAbstract(isAbstract);
      instance.setFinal(isFinal);
      instance.setName(name);
      instance.setStatic(isStatic);
      instance.setVisibility(visibility);
      for (Object child : children) {
         if (child instanceof MemoryClass) {
            instance.addInnerClass((MemoryClass)child);
         }
         else if (child instanceof MemoryInterface) {
            instance.addInnerInterface((MemoryInterface)child);
         }
         else if (child instanceof MemoryEnum) {
            instance.addInnerEnum((MemoryEnum)child);
         }
         else if (child instanceof MemoryAttribute) {
            instance.addAttribute((MemoryAttribute)child);
         }
         else if (child instanceof MemoryMethod) {
            instance.addMethod((MemoryMethod)child);
         }
         else if (child instanceof MemoryConstructor) {
            instance.addConstructor((MemoryConstructor)child);
         }
         else {
            throw new IllegalArgumentException("Unsupported child \"" + child + "\".");
         }
      }
      return instance;
   }
   
   /**
    * Creates a data source {@link IDSInterface}.
    * @param name The name. 
    * @param isStatic The static flag.
    * @param visibility The visibility.
    * @param children The children.
    * @return The created instance.
    */
   protected MemoryInterface createInterface(String name, 
                                             boolean isStatic, 
                                             DSVisibility visibility,
                                             Object...children) {
      MemoryInterface instance = new MemoryInterface();
      instance.setName(name);
      instance.setStatic(isStatic);
      instance.setVisibility(visibility);
      for (Object child : children) {
         if (child instanceof MemoryClass) {
            instance.addInnerClass((MemoryClass)child);
         }
         else if (child instanceof MemoryInterface) {
            instance.addInnerInterface((MemoryInterface)child);
         }
         else if (child instanceof MemoryEnum) {
            instance.addInnerEnum((MemoryEnum)child);
         }
         else if (child instanceof MemoryAttribute) {
            instance.addAttribute((MemoryAttribute)child);
         }
         else if (child instanceof MemoryMethod) {
            instance.addMethod((MemoryMethod)child);
         }
         else {
            throw new IllegalArgumentException("Unsupported child \"" + child + "\".");
         }
      }
      return instance;
   }
   
   /**
    * Creates a data source {@link IDSEnum}.
    * @param name The name. 
    * @param isStatic The static flag.
    * @param visibility The visibility.
    * @param children The children.
    * @return The created instance.
    */
   protected MemoryEnum createEnum(String name, 
                                   boolean isStatic, 
                                   DSVisibility visibility,
                                   Object... children) {
      MemoryEnum instance = new MemoryEnum();
      instance.setName(name);
      instance.setStatic(isStatic);
      instance.setVisibility(visibility);
      for (Object child : children) {
         if (child instanceof MemoryClass) {
            instance.addInnerClass((MemoryClass)child);
         }
         else if (child instanceof MemoryInterface) {
            instance.addInnerInterface((MemoryInterface)child);
         }
         else if (child instanceof MemoryEnum) {
            instance.addInnerEnum((MemoryEnum)child);
         }
         else if (child instanceof MemoryAttribute) {
            instance.addAttribute((MemoryAttribute)child);
         }
         else if (child instanceof MemoryMethod) {
            instance.addMethod((MemoryMethod)child);
         }
         else if (child instanceof MemoryConstructor) {
            instance.addConstructor((MemoryConstructor)child);
         }
         else if (child instanceof MemoryEnumLiteral) {
            instance.addLiteral((MemoryEnumLiteral)child);
         }
         else {
            throw new IllegalArgumentException("Unsupported child \"" + child + "\".");
         }
      }
      return instance;
   }
}