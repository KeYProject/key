/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.api.doc;

import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.KeYResourceManager;
import freemarker.core.HTMLOutputFormat;
import freemarker.ext.beans.ZeroArgumentNonVoidMethodPolicy;
import freemarker.template.Configuration;
import freemarker.template.DefaultObjectWrapper;
import freemarker.template.TemplateException;
import freemarker.template.TemplateExceptionHandler;

import java.io.IOException;
import java.io.StringWriter;
import java.util.*;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * Generation of Markdown documentation.
 *
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public class DocGen implements Supplier<String> {
    private final Metamodel.KeyApi metamodel;

    public DocGen(Metamodel.KeyApi metamodel) {
        this.metamodel = metamodel;
    }

    @Override
    public String get() {
        final StringWriter target = new StringWriter();
        try {
            // 1) Configure FreeMarker
            var cfg = new Configuration(Configuration.VERSION_2_3_32);
            cfg.setClassForTemplateLoading(DocGen.class, "/templates"); // classpath
            cfg.setDefaultEncoding("UTF-8");
            cfg.setAutoEscapingPolicy(Configuration.DISABLE_AUTO_ESCAPING_POLICY);
            cfg.setTemplateExceptionHandler(TemplateExceptionHandler.HTML_DEBUG_HANDLER);
            cfg.setLogTemplateExceptions(false);
            cfg.setWrapUncheckedExceptions(true);
            cfg.setFallbackOnNullLoopVariable(false);
            cfg.setOutputFormat(HTMLOutputFormat.INSTANCE);

            // Use DefaultObjectWrapper to expose fields of objects in the data model
            DefaultObjectWrapper wrapper = new DefaultObjectWrapper(Configuration.VERSION_2_3_32);
            wrapper.setExposeFields(true);
            wrapper.setMethodsShadowItems(true);
            wrapper.setRecordZeroArgumentNonVoidMethodPolicy(
                    ZeroArgumentNonVoidMethodPolicy.BOTH_METHOD_AND_PROPERTY_UNLESS_BEAN_PROPERTY_READ_METHOD);
            wrapper.setForceLegacyNonListCollections(false);
            wrapper.setDefaultDateType(freemarker.template.TemplateDateModel.DATETIME);
            cfg.setObjectWrapper(wrapper);

            // 2) Build the data-model
            Map<String, Object> model = new TreeMap<>();

            model.put("segmentDocumentation", metamodel.segmentDocumentation());

            model.put("endpoints",
                    metamodel.endpoints()
                            .stream().sorted(Comparator.comparing(Metamodel.Endpoint::name))
                            .toList());

            final Map<String, List<Metamodel.Endpoint>> collect = metamodel.endpoints()
                    .stream().sorted(Comparator.comparing(Metamodel.Endpoint::name))
                    .collect(Collectors.groupingBy(Metamodel.Endpoint::segment, TreeMap::new, Collectors.toList()));

            model.put("endpointsBySegment", collect);

            model.put("types",
                    metamodel.types().values()
                            .stream().sorted(Comparator.comparing(Metamodel.Type::name))
                            .toList());

            model.put("version",
                    KeYResourceManager.getManager().getVersion() +
                            " (" + KeYConstants.INTERNAL_VERSION.substring(0, 8) + ")");
            model.put("date", new Date());

            // 3) Get template
            var tpl = cfg.getTemplate("docs.ftl");

            // 4) Merge and output
            tpl.process(model, target);
            return target.toString();
        } catch (IOException | TemplateException e) {
            throw new RuntimeException(e);
        }
    }
}
