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

package de.hentschel.visualdbc.dbcmodel.diagram.part;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.eclipse.gef.Tool;
import org.eclipse.gef.palette.PaletteContainer;
import org.eclipse.gef.palette.PaletteDrawer;
import org.eclipse.gef.palette.PaletteRoot;
import org.eclipse.gef.palette.ToolEntry;
import org.eclipse.gmf.runtime.diagram.ui.tools.UnspecifiedTypeConnectionTool;
import org.eclipse.gmf.runtime.diagram.ui.tools.UnspecifiedTypeCreationTool;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;

import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbCPaletteFactory {

   /**
    * @generated
    */
   public void fillPalette(PaletteRoot paletteRoot) {
      paletteRoot.add(createCode1Group());
      paletteRoot.add(createSpecification2Group());
      paletteRoot.add(createProof3Group());
   }

   /**
    * Creates "Code" palette tool group
    * @generated
    */
   private PaletteContainer createCode1Group() {
      PaletteDrawer paletteContainer = new PaletteDrawer(
            Messages.Code1Group_title);
      paletteContainer.setId("createCode1Group"); //$NON-NLS-1$
      paletteContainer.add(createPackage1CreationTool());
      paletteContainer.add(createClass2CreationTool());
      paletteContainer.add(createInterface3CreationTool());
      paletteContainer.add(createEnum4CreationTool());
      paletteContainer.add(createEnumLiteral5CreationTool());
      paletteContainer.add(createAttribute6CreationTool());
      paletteContainer.add(createMethod7CreationTool());
      paletteContainer.add(createConstructor8CreationTool());
      paletteContainer.add(createExtends9CreationTool());
      paletteContainer.add(createImplements10CreationTool());
      return paletteContainer;
   }

   /**
    * Creates "Specification" palette tool group
    * @generated
    */
   private PaletteContainer createSpecification2Group() {
      PaletteDrawer paletteContainer = new PaletteDrawer(
            Messages.Specification2Group_title);
      paletteContainer.setId("createSpecification2Group"); //$NON-NLS-1$
      paletteContainer.add(createAxiom1CreationTool());
      paletteContainer.add(createAxiomContract2CreationTool());
      paletteContainer.add(createInvariant3CreationTool());
      paletteContainer.add(createOperationContract4CreationTool());
      return paletteContainer;
   }

   /**
    * Creates "Proof" palette tool group
    * @generated
    */
   private PaletteContainer createProof3Group() {
      PaletteDrawer paletteContainer = new PaletteDrawer(
            Messages.Proof3Group_title);
      paletteContainer.setId("createProof3Group"); //$NON-NLS-1$
      paletteContainer.add(createProof1CreationTool());
      paletteContainer.add(createProofTarget2CreationTool());
      paletteContainer.add(createProofReference3CreationTool());
      return paletteContainer;
   }

   /**
    * @generated
    */
   private ToolEntry createPackage1CreationTool() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(2);
      types.add(DbCElementTypes.DbcPackage_2007);
      types.add(DbCElementTypes.DbcPackage_3027);
      NodeToolEntry entry = new NodeToolEntry(
            Messages.Package1CreationTool_title,
            Messages.Package1CreationTool_desc, types);
      entry.setId("createPackage1CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcPackage_2007));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createClass2CreationTool() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(2);
      types.add(DbCElementTypes.DbcClass_3031);
      types.add(DbCElementTypes.DbcClass_2012);
      NodeToolEntry entry = new NodeToolEntry(
            Messages.Class2CreationTool_title,
            Messages.Class2CreationTool_desc, types);
      entry.setId("createClass2CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcClass_3031));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createInterface3CreationTool() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(2);
      types.add(DbCElementTypes.DbcInterface_3032);
      types.add(DbCElementTypes.DbcInterface_2011);
      NodeToolEntry entry = new NodeToolEntry(
            Messages.Interface3CreationTool_title,
            Messages.Interface3CreationTool_desc, types);
      entry.setId("createInterface3CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcInterface_3032));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createEnum4CreationTool() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(2);
      types.add(DbCElementTypes.DbcEnum_3033);
      types.add(DbCElementTypes.DbcEnum_2013);
      NodeToolEntry entry = new NodeToolEntry(Messages.Enum4CreationTool_title,
            Messages.Enum4CreationTool_desc, types);
      entry.setId("createEnum4CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcEnum_3033));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createEnumLiteral5CreationTool() {
      NodeToolEntry entry = new NodeToolEntry(
            Messages.EnumLiteral5CreationTool_title,
            Messages.EnumLiteral5CreationTool_desc,
            Collections.singletonList(DbCElementTypes.DbcEnumLiteral_3020));
      entry.setId("createEnumLiteral5CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcEnumLiteral_3020));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createAttribute6CreationTool() {
      NodeToolEntry entry = new NodeToolEntry(
            Messages.Attribute6CreationTool_title,
            Messages.Attribute6CreationTool_desc,
            Collections.singletonList(DbCElementTypes.DbcAttribute_3011));
      entry.setId("createAttribute6CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcAttribute_3011));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createMethod7CreationTool() {
      NodeToolEntry entry = new NodeToolEntry(
            Messages.Method7CreationTool_title,
            Messages.Method7CreationTool_desc,
            Collections.singletonList(DbCElementTypes.DbcMethod_3009));
      entry.setId("createMethod7CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcMethod_3009));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createConstructor8CreationTool() {
      NodeToolEntry entry = new NodeToolEntry(
            Messages.Constructor8CreationTool_title,
            Messages.Constructor8CreationTool_desc,
            Collections.singletonList(DbCElementTypes.DbcConstructor_3010));
      entry.setId("createConstructor8CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcConstructor_3010));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createExtends9CreationTool() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(2);
      types.add(DbCElementTypes.DbcClassExtends_4003);
      types.add(DbCElementTypes.DbcInterfaceExtends_4004);
      LinkToolEntry entry = new LinkToolEntry(
            Messages.Extends9CreationTool_title,
            Messages.Extends9CreationTool_desc, types);
      entry.setId("createExtends9CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCDiagramEditorPlugin
            .findImageDescriptor("/de.hentschel.visualdbc.dbcmodel/icons/extends.gif")); //$NON-NLS-1$
      entry.setLargeIcon(DbCDiagramEditorPlugin
            .findImageDescriptor("/de.hentschel.visualdbc.dbcmodel/icons/extends.gif")); //$NON-NLS-1$
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createImplements10CreationTool() {
      LinkToolEntry entry = new LinkToolEntry(
            Messages.Implements10CreationTool_title,
            Messages.Implements10CreationTool_desc,
            Collections
                  .singletonList(DbCElementTypes.AbstractDbcClassImplements_4005));
      entry.setId("createImplements10CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCDiagramEditorPlugin
            .findImageDescriptor("/de.hentschel.visualdbc.dbcmodel/icons/implements.gif")); //$NON-NLS-1$
      entry.setLargeIcon(DbCDiagramEditorPlugin
            .findImageDescriptor("/de.hentschel.visualdbc.dbcmodel/icons/implements.gif")); //$NON-NLS-1$
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createAxiom1CreationTool() {
      NodeToolEntry entry = new NodeToolEntry(
            Messages.Axiom1CreationTool_title,
            Messages.Axiom1CreationTool_desc,
            Collections.singletonList(DbCElementTypes.DbcAxiom_3036));
      entry.setId("createAxiom1CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcAxiom_3036));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createAxiomContract2CreationTool() {
      NodeToolEntry entry = new NodeToolEntry(
            Messages.AxiomContract2CreationTool_title,
            Messages.AxiomContract2CreationTool_desc,
            Collections.singletonList(DbCElementTypes.DbCAxiomContract_3037));
      entry.setId("createAxiomContract2CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbCAxiomContract_3037));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createInvariant3CreationTool() {
      NodeToolEntry entry = new NodeToolEntry(
            Messages.Invariant3CreationTool_title,
            Messages.Invariant3CreationTool_desc,
            Collections.singletonList(DbCElementTypes.DbcInvariant_3035));
      entry.setId("createInvariant3CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcInvariant_3035));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createOperationContract4CreationTool() {
      NodeToolEntry entry = new NodeToolEntry(
            Messages.OperationContract4CreationTool_title,
            Messages.OperationContract4CreationTool_desc,
            Collections
                  .singletonList(DbCElementTypes.DbcOperationContract_3026));
      entry.setId("createOperationContract4CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcOperationContract_3026));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createProof1CreationTool() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(2);
      types.add(DbCElementTypes.DbcProof_3034);
      types.add(DbCElementTypes.DbcProof_2014);
      NodeToolEntry entry = new NodeToolEntry(
            Messages.Proof1CreationTool_title,
            Messages.Proof1CreationTool_desc, types);
      entry.setId("createProof1CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCElementTypes
            .getImageDescriptor(DbCElementTypes.DbcProof_3034));
      entry.setLargeIcon(entry.getSmallIcon());
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createProofTarget2CreationTool() {
      LinkToolEntry entry = new LinkToolEntry(
            Messages.ProofTarget2CreationTool_title,
            Messages.ProofTarget2CreationTool_desc,
            Collections.singletonList(DbCElementTypes.DbcProofTarget_4001));
      entry.setId("createProofTarget2CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCDiagramEditorPlugin
            .findImageDescriptor("/de.hentschel.visualdbc.dbcmodel/icons/proofTarget.gif")); //$NON-NLS-1$
      entry.setLargeIcon(DbCDiagramEditorPlugin
            .findImageDescriptor("/de.hentschel.visualdbc.dbcmodel/icons/proofTarget.gif")); //$NON-NLS-1$
      return entry;
   }

   /**
    * @generated
    */
   private ToolEntry createProofReference3CreationTool() {
      LinkToolEntry entry = new LinkToolEntry(
            Messages.ProofReference3CreationTool_title,
            Messages.ProofReference3CreationTool_desc,
            Collections.singletonList(DbCElementTypes.DbcProofReference_4002));
      entry.setId("createProofReference3CreationTool"); //$NON-NLS-1$
      entry.setSmallIcon(DbCDiagramEditorPlugin
            .findImageDescriptor("/de.hentschel.visualdbc.dbcmodel/icons/proofReference.gif")); //$NON-NLS-1$
      entry.setLargeIcon(DbCDiagramEditorPlugin
            .findImageDescriptor("/de.hentschel.visualdbc.dbcmodel/icons/proofReference.gif")); //$NON-NLS-1$
      return entry;
   }

   /**
    * @generated
    */
   private static class NodeToolEntry extends ToolEntry {

      /**
       * @generated
       */
      private final List<IElementType> elementTypes;

      /**
       * @generated
       */
      private NodeToolEntry(String title, String description,
            List<IElementType> elementTypes) {
         super(title, description, null, null);
         this.elementTypes = elementTypes;
      }

      /**
       * @generated
       */
      public Tool createTool() {
         Tool tool = new UnspecifiedTypeCreationTool(elementTypes);
         tool.setProperties(getToolProperties());
         return tool;
      }
   }

   /**
    * @generated
    */
   private static class LinkToolEntry extends ToolEntry {

      /**
       * @generated
       */
      private final List<IElementType> relationshipTypes;

      /**
       * @generated
       */
      private LinkToolEntry(String title, String description,
            List<IElementType> relationshipTypes) {
         super(title, description, null, null);
         this.relationshipTypes = relationshipTypes;
      }

      /**
       * @generated
       */
      public Tool createTool() {
         Tool tool = new UnspecifiedTypeConnectionTool(relationshipTypes);
         tool.setProperties(getToolProperties());
         return tool;
      }
   }
}