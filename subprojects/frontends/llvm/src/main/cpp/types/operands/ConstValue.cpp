//
// Created by solarowl on 3/30/21.
//

#include "ConstValue.h"
#include <sstream>
#include <string>
#include <iostream>

ConstValue::ConstValue(llvm::Value &llvmConstValue) {
    llvm::raw_string_ostream nameStream(name);
    llvmConstValue.print(nameStream); //
    nameStream.str();

    // function pointers can have whitespaces in their type names, which we do not handle, so we change them to _
    // the last whitespace should remain though, as that is the delimiter between the type and the function name
    std::vector<std::string> words;
    std::stringstream check1(name);
    std::string intermediate;

    // Tokenizing w.r.t. space ' '
    while(getline(check1, intermediate, ' '))
    {
        words.push_back(intermediate);
    }

    std::ostringstream os;
    if(words.size()>2) {
        for(unsigned int i = 0; i < words.size()-1; i++)
            os << words[i] << "_";
        os << " " << words[words.size()-1];
        name = os.str();

    } // else we change nothing in the name

}