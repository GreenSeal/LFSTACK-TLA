#ifndef LFStackLA_STACK_H
#define LFStackLA_STACK_H

#include<iostream>
#include<atomic>

class LFStack {
public:
    //the node type in the stack
    typedef struct _Node
    {
        int data = 0;
        struct _Node* next = nullptr;
    } Node;

    std::atomic<Node*> head{nullptr};

    //the push function
    void push(int value)
    {
        Node *node = new Node();
        node->data = value;
        auto* old = head.load();
        do {
            old = head.load();
            node->next = old;
        } while (!head.compare_exchange_weak(old, node));
    }

    int pop()
    {
        auto* locHead = head.load();
        Node* nextHead;
        do{
            locHead = head.load();
            if(locHead == nullptr) //return when the stack is empty
            {
                return -1;
            }
            nextHead = locHead->next;
        } while(!head.compare_exchange_weak(locHead, nextHead));
        //std::cout << "poping value " << orig->head->data << std::endl;
        auto res = locHead->data;
        delete locHead;
        return res;
    }
};

#endif //LFStackLA_STACK_H
