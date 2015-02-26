
#include <functional>
#include <vector>

#include <llvm/Support/raw_ostream.h>

using namespace std;

namespace VVT {


class BitVector {
    char *bits;
    size_t Num;
    size_t Size;

public:

    class bitref {

        friend class BitVector;

        char* byte;
        size_t  pos;

        static inline const size_t
        bit_pos (size_t index)
        {
            return index & 7;
        }

        static inline const size_t
        byte_index (size_t index)
        {
            return index >> 3;
        }

        static inline unsigned char
        mask (size_t pos)
        {
            return (1 << pos);
        }

        public:
        bitref(BitVector& b, size_t index)
        {
            byte = &b.bits[byte_index(index)];
            pos = bit_pos(index);
        }

        // For b[i] = __x;
        bitref &
        operator=(bool v)
        {
            if (v)
              *byte |= mask(pos);
            else
              *byte &= ~mask(pos);
            return *this;
        }

        // For b[i] = b[__j];
        bitref&
        operator=(const bitref& x)
        {
            if ((*(x.byte) & mask(x.pos)))
                *byte |= mask(pos);
            else
                *byte &= ~mask(pos);
            return *this;
        }

        // Flips the bit
        bool
        operator~() const
        {
            return (*(byte) & mask(pos)) == 0;
        }

        // For __x = b[i];
        operator bool() const
        { return (*(byte) & mask(pos)) != 0; }

        // For b[i].flip();
        bitref&
        flip()
        {
            *byte ^= mask (pos);
            return *this;
        }
    };

    BitVector();
    BitVector(int size);
    BitVector(BitVector *other, int size);
    BitVector(BitVector *other);
    ~BitVector();

    bitref operator[](int x);
    const bool operator[](int x) const;
    BitVector &operator|=(BitVector &x);

    void print (llvm::raw_ostream &outs, size_t max);
    void print (llvm::raw_ostream &outs);
    void ensure (size_t size);
};

class BitMatrix {
    vector<BitVector *> rows;
    int ColSize,RowSize;
    int ColsMax,RowsMax;

public:
    BitMatrix(int init_cols, int init_rows);
    ~BitMatrix();

    void copy (int row_to, int row);
    void set (int col, int row);
    bool get (int col, int row);
    void ensure (int new_cols, int new_rows);

    void print (llvm::raw_ostream &outs);
};



}
