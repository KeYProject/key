package de.uka.ilkd.key.lang.clang.common.programmeta;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.Name;

/**
 * Program meta construct builder.
 * @author oleg.myrk@gmail.com
 */
public class ProgamMetaBuilder {
        
        /**
         * Builds a map from program meta construct names to thir classes. 
         * @return
         */
        public static Map buildMap() {
                Map map = new HashMap();

                put(map, EnterBlockFrameProgramMeta.buildName(), EnterBlockFrameProgramMeta.class);
                put(map, IntroduceBlockFrameVarDeclProgramMeta.buildName(), IntroduceBlockFrameVarDeclProgramMeta.class);
                put(map, UnwindBlockFrameProgramMeta.buildName(), UnwindBlockFrameProgramMeta.class);
                
                return map;
        }
        
        private static void put(Map map, Name name, Class clazz) {
                map.put(name, clazz);
        }
}
