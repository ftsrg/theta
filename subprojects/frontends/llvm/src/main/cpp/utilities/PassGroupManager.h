//
// Created by solarowl on 3/30/21.
//

#ifndef JNI_LIBRARY_PASSGROUPMANAGER_H
#define JNI_LIBRARY_PASSGROUPMANAGER_H

class PassGroupManager {
public:
    static bool enableInlining; // true by default
    static bool enableOptimizations; // true by default
    static bool enableCleanupPasses; // true by default
    static bool debugPrintIr; // true by default
    PassGroupManager() = delete;
};


#endif //JNI_LIBRARY_PASSGROUPMANAGER_H
