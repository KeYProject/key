package org.key_project.key4eclipse.resources.projectinfo;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.Deque;
import java.util.LinkedList;
import java.util.Map;
import java.util.WeakHashMap;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo.ContractModality;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.XMLUtil;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * This singleton manages {@link ProjectInfo}s of {@link IProject}s which
 * means that it provides for each {@link IProject} the only instance of
 * {@link ProjectInfo} and allows to save and laod {@link ProjectInfo}s on demand.
 * @author Martin Hentschel
 */
public final class ProjectInfoManager {
   /**
    * The file name within the proof folder used to store a {@link ProjectInfo}.
    */
   public static final String PROJECT_INFO_FILE = ".projectinfo";

   /**
    * Tag name to store {@link ProjectInfo}s.
    */
   private static final String TAG_PROJECT_INFO = "project";

   /**
    * Tag name to store {@link PackageInfo}s.
    */
   private static final String TAG_PACKAGE_INFO = "package";

   /**
    * Tag name to store {@link TypeInfo}s.
    */
   private static final String TAG_TYPE_INFO = "type";

   /**
    * Tag name to store {@link MethodInfo}s.
    */
   private static final String TAG_METHOD_INFO = "method";

   /**
    * Tag name to store {@link ContractInfo}s.
    */
   private static final String TAG_CONTRACT_INFO = "contract";

   /**
    * Tag name to store {@link ObserverFunctionInfo}s.
    */
   private static final String TAG_OBSERVER_FUNCTION_INFO = "obsererFunction";

   /**
    * Attribute name to store a name.
    */
   private static final String ATTRIBUTE_NAME = "name";

   /**
    * Attribute name to store a path.
    */
   private static final String ATTRIBUTE_PATH = "path";

   /**
    * Attribute name to store a display name.
    */
   private static final String ATTRIBUTE_DISPLAY_NAME = "displayName";

   /**
    * Attribute name to store parameter types.
    */
   private static final String ATTRIBUTE_PARAMETER_TYPES = "parameterTypes";

   /**
    * Attribute name to store a proof file path.
    */
   private static final String ATTRIBUTE_PROOF_FILE_PATH = "proofFilePath";

   /**
    * Attribute name to store a meta file path.
    */
   private static final String ATTRIBUTE_META_FILE_PATH = "metaFilePath";

   /**
    * Attribute name to store a modality.
    */
   private static final String ATTRIBUTE_MODALITY = "modality";
   
   /**
    * Maps each {@link IProject} to its {@link ProjectInfo}.
    */
   private final WeakHashMap<IProject, ProjectInfo> infos = new WeakHashMap<IProject, ProjectInfo>();

   /**
    * The only instance of this class.
    */
   private static final ProjectInfoManager instance = new ProjectInfoManager();
   
   /**
    * Constructor to forbid other instances.
    */
   private ProjectInfoManager() {
   }
   
   /**
    * Returns the {@link ProjectInfo} related to the given {@link IProject}.
    * If not cached before it is loaded from the info file ({@link #PROJECT_INFO_FILE})
    * if available or freshly created otherwise.
    * @param project The {@link IProject} for which the {@link ProjectInfo} is requested.
    * @return The {@link ProjectInfo} related to the given {@link IProject}.
    */
   public ProjectInfo getProjectInfo(IProject project) {
      synchronized (this) {
         ProjectInfo info = infos.get(project);
         if (info == null) {
            // Try to load info
            IFolder proofFolder = project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
            if (proofFolder.exists()) {
               IFile infoFile = proofFolder.getFile(PROJECT_INFO_FILE);
               if (infoFile.exists()) {
                  try {
                     info = load(infoFile);
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
            // Create new info if loading failed
            if (info == null) {
               info = new ProjectInfo();
            }
            info.mapResource(project, info);
            infos.put(project, info);
         }
         return info;
      }
   }
   
   /**
    * Loads the {@link ProjectInfo} from the given {@link IFile}.
    * @param file The {@link IFile} to load from.
    * @return The loaded {@link ProjectInfo} or {@code null} if not available.
    * @throws Exception Occurred Exception.
    */
   public static ProjectInfo load(IFile file) throws Exception {
      if (file != null) {
         return load(file.getContents());
      }
      else {
         return null;
      }
   }
   
   /**
    * Loads the {@link ProjectInfo} from the given {@link InputStream}.
    * @param in The {@link InputStream} to read from.
    * @return The loaded {@link ProjectInfo} or {@code null} if not available.
    * @throws Exception Occurred Exception.
    */
   public static ProjectInfo load(InputStream in) throws Exception {
      if (in != null) {
         try {
            // Parse XML document
            SAXParserFactory factory = SAXParserFactory.newInstance();
            factory.setNamespaceAware(true);
            SAXParser saxParser = factory.newSAXParser();
            InfoSAXHandler handler = new InfoSAXHandler();
            saxParser.parse(in, handler);
            // Return result
            return handler.getProjectInfo();
         }
         finally {
            in.close();
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Utility class used by {@link ProjectInfoManager#load(IFile)}.
    * @author Martin Hentschel
    */
   private static class InfoSAXHandler extends DefaultHandler {
      /**
       * The loaded {@link ProjectInfo}.
       */
      private ProjectInfo projectInfo;
      
      /**
       * The parent hierarchy filled by {@link #startElement(String, String, String, Attributes)}
       * and emptied by {@link #endElement(String, String, String)}.
       */
      private final Deque<Object> parentStack = new LinkedList<Object>();

      /**
       * {@inheritDoc}
       */
      @Override
      public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
         if (TAG_PROJECT_INFO.equals(qName)) {
            Assert.isTrue(projectInfo == null);
            projectInfo = new ProjectInfo();
            parentStack.addFirst(projectInfo);
         }
         else if (TAG_PACKAGE_INFO.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent == projectInfo);
            PackageInfo packageInfo = new PackageInfo(projectInfo, getName(attributes), getContainer(attributes));
            projectInfo.addPackage(packageInfo, projectInfo.countPackages());
            parentStack.addFirst(packageInfo);
         }
         else if (TAG_TYPE_INFO.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent instanceof AbstractTypeContainer);
            AbstractTypeContainer tcInfo = (AbstractTypeContainer) parent;
            TypeInfo typeInfo = new TypeInfo(projectInfo, getName(attributes), getFile(attributes), tcInfo);
            tcInfo.addType(typeInfo, tcInfo.countTypes());
            parentStack.addFirst(typeInfo);
         }
         else if (TAG_METHOD_INFO.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent instanceof TypeInfo);
            TypeInfo typeInfo = (TypeInfo) parent;
            MethodInfo methodInfo = new MethodInfo(projectInfo, typeInfo, getDisplayName(attributes), getName(attributes), getParameterTypes(attributes));
            typeInfo.addMethod(methodInfo, typeInfo.countMethods());
            parentStack.addFirst(methodInfo);
         }
         else if (TAG_OBSERVER_FUNCTION_INFO.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent instanceof TypeInfo);
            TypeInfo typeInfo = (TypeInfo) parent;
            ObserverFunctionInfo observerFunctionInfo = new ObserverFunctionInfo(projectInfo, typeInfo, getDisplayName(attributes));
            typeInfo.addObserverFunction(observerFunctionInfo, typeInfo.countObserverFunctions());
            parentStack.addFirst(observerFunctionInfo);
         }
         else if (TAG_CONTRACT_INFO.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent instanceof AbstractContractContainer);
            AbstractContractContainer ccInfo = (AbstractContractContainer) parent;
            ContractInfo contractInfo = new ContractInfo(ccInfo, getName(attributes), getModality(attributes), getProofFile(attributes), getMetaFile(attributes));
            ccInfo.addContract(contractInfo, ccInfo.countContracts());
            parentStack.addFirst(contractInfo);
         }
         else {
            Assert.isTrue(false, "Unsupported tag \"" + qName + "\".");
         }
      }
      
      /**
       * Returns the container.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected IContainer getContainer(Attributes attributes) {
         String path = attributes.getValue(ATTRIBUTE_PATH);
         if (path != null) {
            Path resourcePath = new Path(path);
            if (resourcePath.segmentCount() == 1) {
               return ResourcesPlugin.getWorkspace().getRoot().getProject(path);
            }
            else {
               return ResourcesPlugin.getWorkspace().getRoot().getFolder(new Path(path));
            }
         }
         else {
            return null;
         }
      }

      /**
       * Returns the file.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected IFile getFile(Attributes attributes) {
         String path = attributes.getValue(ATTRIBUTE_PATH);
         if (path != null) {
            return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(path));
         }
         else {
            return null;
         }
      }

      /**
       * Returns the name.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getName(Attributes attributes) {
         return attributes.getValue(ATTRIBUTE_NAME);
      }

      /**
       * Returns the parameter types.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String[] getParameterTypes(Attributes attributes) {
         String types = attributes.getValue(ATTRIBUTE_PARAMETER_TYPES);
         if (!StringUtil.isTrimmedEmpty(types)) {
            return types.split(";");
         }
         else {
            return new String[0];
         }
      }

      /**
       * Returns the display name.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getDisplayName(Attributes attributes) {
         return attributes.getValue(ATTRIBUTE_DISPLAY_NAME);
      }

      /**
       * Returns the proof file.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      public IFile getProofFile(Attributes attributes) {
         String path = attributes.getValue(ATTRIBUTE_PROOF_FILE_PATH);
         if (path != null) {
            return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(path));
         }
         else {
            return null;
         }
      }

      /**
       * Returns the meta file.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      public IFile getMetaFile(Attributes attributes) {
         String path = attributes.getValue(ATTRIBUTE_META_FILE_PATH);
         if (path != null) {
            return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(path));
         }
         else {
            return null;
         }
      }

      /**
       * Returns the modality.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      public ContractModality getModality(Attributes attributes) {
         String modality = attributes.getValue(ATTRIBUTE_MODALITY);
         if (modality != null) {
            return ContractModality.valueOf(modality);
         }
         else {
            return null;
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void endElement(String uri, String localName, String qName) throws SAXException {
         if (!parentStack.isEmpty()) {
            parentStack.removeFirst();
         }
      }

      /**
       * Returns the loaded {@link ProjectInfo}.
       * @return The loaded {@link ProjectInfo}.
       */
      public ProjectInfo getProjectInfo() {
         return projectInfo;
      }
   }

   /**
    * Saves the given {@link ProjectInfo} back to the {@link IProject}.
    * @param project The {@link IProject} to save {@link ProjectInfo} in.
    * @param info The {@link ProjectInfo} to save.
    * @throws CoreException Occurred Exception.
    */
   public void save(IProject project, ProjectInfo info) throws CoreException {
      Assert.isTrue(info == infos.get(project));
      if (project.exists() && project.isOpen()) {
         InputStream in = null;
         try {
            Charset charset = Charset.defaultCharset();
            String xml = toXML(charset, info);
            in = new ByteArrayInputStream(xml.getBytes(charset));
            IFolder proofFolder = project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
            if (!proofFolder.exists()) {
               proofFolder.create(true, true, null);
            }
            IFile file = proofFolder.getFile(PROJECT_INFO_FILE);
            if (file.exists()) {
               file.setContents(in, true, true, null);
            }
            else {
               file.create(in, true, null);
            }
            file.setCharset(charset.displayName(), null);
         }
         finally {
            try {
               if (in != null) {
                  in.close();
               }
            }
            catch (IOException e) {
               throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
            }
         }
      }
   }

   /**
    * Converts the given {@link ProjectInfo} into XML.
    * @param charset The {@link Character} to use.
    * @param info The {@link ProjectInfo} to convert.
    * @return The XML content.
    */
   private String toXML(Charset charset, ProjectInfo info) {
      StringBuffer sb = new StringBuffer();
      XMLUtil.appendXmlHeader(charset.displayName(), sb);
      XMLUtil.appendStartTag(0, TAG_PROJECT_INFO, null, sb);
      for (PackageInfo packageInfo : info.getPackages()) {
         appendPackageInfo(1, packageInfo, sb);
      }
      XMLUtil.appendEndTag(0, TAG_PROJECT_INFO, sb);
      return sb.toString();
   }

   /**
    * Appends the given {@link PackageInfo} as XML to the given {@link StringBuffer}.
    * @param level The level.
    * @param packageInfo the {@link PackageInfo} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   private void appendPackageInfo(int level, PackageInfo packageInfo, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, packageInfo.getName());
      if (packageInfo.getContainer() != null) {
         attributeValues.put(ATTRIBUTE_PATH, packageInfo.getContainer().getFullPath().toString());         
      }
      XMLUtil.appendStartTag(level, TAG_PACKAGE_INFO, attributeValues, sb);
      for (TypeInfo typeInfo : packageInfo.getTypes()) {
         appendTypeInfo(level + 1, typeInfo, sb);
      }
      XMLUtil.appendEndTag(level, TAG_PACKAGE_INFO, sb);
   }

   /**
    * Appends the given {@link TypeInfo} as XML to the given {@link StringBuffer}.
    * @param level The level.
    * @param typeInfo the {@link TypeInfo} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   private void appendTypeInfo(int level, TypeInfo typeInfo, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, typeInfo.getName());
      if (typeInfo.getFile() != null) {
         attributeValues.put(ATTRIBUTE_PATH, typeInfo.getFile().getFullPath().toString());         
      }
      XMLUtil.appendStartTag(level, TAG_TYPE_INFO, attributeValues, sb);
      for (MethodInfo methodInfo : typeInfo.getMethods()) {
         appendMethodInfo(level + 1, methodInfo, sb);
      }
      for (ObserverFunctionInfo observerFunctionInfo : typeInfo.getObserverFunctions()) {
         appendObserverFunctionInfo(level + 1, observerFunctionInfo, sb);
      }
      for (TypeInfo internalTypeInfo : typeInfo.getTypes()) {
         appendTypeInfo(level + 1, internalTypeInfo, sb);
      }
      XMLUtil.appendEndTag(level, TAG_TYPE_INFO, sb);
   }

   /**
    * Appends the given {@link MethodInfo} as XML to the given {@link StringBuffer}.
    * @param level The level.
    * @param methodInfo the {@link MethodInfo} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   private void appendMethodInfo(int level, MethodInfo methodInfo, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_DISPLAY_NAME, methodInfo.getDisplayName());
      attributeValues.put(ATTRIBUTE_NAME, methodInfo.getName());
      attributeValues.put(ATTRIBUTE_PARAMETER_TYPES, ArrayUtil.toString(methodInfo.getParameterTypes(), ";"));
      XMLUtil.appendStartTag(level, TAG_METHOD_INFO, attributeValues, sb);
      for (ContractInfo contractInfo : methodInfo.getContracts()) {
         appendContractInfo(level + 1, contractInfo, sb);
      }
      XMLUtil.appendEndTag(level, TAG_METHOD_INFO, sb);
   }

   /**
    * Appends the given {@link ObserverFunctionInfo} as XML to the given {@link StringBuffer}.
    * @param level The level.
    * @param observerFunctionInfo the {@link ObserverFunctionInfo} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   private void appendObserverFunctionInfo(int level, ObserverFunctionInfo observerFunctionInfo, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_DISPLAY_NAME, observerFunctionInfo.getDisplayName());
      XMLUtil.appendStartTag(level, TAG_OBSERVER_FUNCTION_INFO, attributeValues, sb);
      for (ContractInfo contractInfo : observerFunctionInfo.getContracts()) {
         appendContractInfo(level + 1, contractInfo, sb);
      }
      XMLUtil.appendEndTag(level, TAG_OBSERVER_FUNCTION_INFO, sb);
   }

   /**
    * Appends the given {@link ContractInfo} as XML to the given {@link StringBuffer}.
    * @param level The level.
    * @param contractInfo the {@link ContractInfo} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   private void appendContractInfo(int level, ContractInfo contractInfo, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, contractInfo.getName());
      if (contractInfo.getModality() != null) {
         attributeValues.put(ATTRIBUTE_MODALITY, contractInfo.getModality().toString());
      }
      if (contractInfo.getProofFile() != null) {
         attributeValues.put(ATTRIBUTE_PROOF_FILE_PATH, contractInfo.getProofFile().getFullPath().toString());
      }
      if (contractInfo.getMetaFile() != null) {
         attributeValues.put(ATTRIBUTE_META_FILE_PATH, contractInfo.getMetaFile().getFullPath().toString());
      }
      XMLUtil.appendEmptyTag(level, TAG_CONTRACT_INFO, attributeValues, sb);
   }

   /**
    * Returns the only instance of this class.
    * @return The only instance.
    */
   public static ProjectInfoManager getInstance() {
      return instance;
   }
   
   /**
    * Returns the parent model element.
    * @param element The current model element.
    * @return The parent model element if available or {@code null} otherwise.
    */
   public static Object getParent(Object element) {
      if (element instanceof ContractInfo) {
         return ((ContractInfo) element).getParent();
      }
      else if (element instanceof MethodInfo) {
         return ((MethodInfo) element).getParent();
      }
      else if (element instanceof ObserverFunctionInfo) {
         return ((ObserverFunctionInfo) element).getParent();
      }
      else if (element instanceof TypeInfo) {
         return ((TypeInfo) element).getParent();
      }
      else if (element instanceof PackageInfo) {
         return ((PackageInfo) element).getProjectInfo();
      }
      else {
         return null;
      }
   }

   /**
    * Checks if the given {@link IFile} is the project info file ({@link #PROJECT_INFO_FILE}). 
    * @param file The {@link IFile} to check.
    * @return {@code true} is info file, {@code false} is something else.
    * @throws CoreException Occurred Exception.
    */
   public boolean isProjectInfoFile(IFile file) throws CoreException {
      if (file != null) {
         return PROJECT_INFO_FILE.equals(file.getName()) &&
                file.getParent() instanceof IFolder &&
                KeYResourcesUtil.isProofFolder((IFolder)file.getParent());
      }
      else {
         return false;
      }
   }
}
