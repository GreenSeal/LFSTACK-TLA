#include "stack.h"
#include <thread>
#include <mutex>
#include <vector>

std::mutex m_;

void push(LFStack& stack, int value) {
    for(int i=0; i<1; i++) {
        stack.push(value);
        std::lock_guard<std::mutex> lg(m_);
        std::cout << "push " << value << std::endl;
    }
}

void pop(LFStack& stack)
{
    for(int i=0; i<1; ++i) {
        int result;
        do{
            result = stack.pop();
        } while(result == -1);
        std::lock_guard<std::mutex> lg(m_);
        std::cout << "pop " << result << std::endl;
    }
}

int main() {
    LFStack stack;
    std::vector<std::thread> workers;

    for(int i=0; i<8; i++) {
        workers.emplace_back(push, std::ref(stack), i);
        workers.emplace_back(pop, std::ref(stack));
    }
    for(auto& w: workers)
        w.join();
    return 0;
}