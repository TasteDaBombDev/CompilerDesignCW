#include "llvm/IR/Instructions.h"
#include <map>

class LinkedTable
{

public:
    std::map<std::string, std::pair<std::string, llvm::Value *> *> table;
    LinkedTable *prevTable;

    LinkedTable(LinkedTable *prev)
    {
        // table = new std::map<std::string, std::pair<std::string, llvm::Value *>* >();
        prevTable = prev;
    }

    void put(std::string name, std::string type, llvm::Value *v)
    {
        table[name] = new std::pair<std::string, llvm::Value *>(type, v);
        // std::cout<< "-----> [INFO] Variable added: " << name << " of type " << type << std::endl;
    }

    std::pair<std::string, llvm::Value *> *get(std::string name)
    {
        for (LinkedTable *k = this; k != nullptr; k = k->prevTable)
        {
            if (k->table[name] != nullptr)
            {
                return k->table[name];
            }
        }
        return nullptr;
    }
};