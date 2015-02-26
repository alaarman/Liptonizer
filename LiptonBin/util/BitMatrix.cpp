
#include <bitset>
#include <assert.h>
#include <iostream>
#include <string>

#include "BitMatrix.h"
#include "Util.h"



using namespace std;

namespace VVT {

BitVector::BitVector()
{
    Num = Size = 0;
    bits = NULL;
}

BitVector::BitVector(int size) : BitVector()
{
    ensure (size);
}

BitVector::BitVector(BitVector *other, int size) : BitVector(size)
{
    assert (other->Size <= Size);
    memcpy (bits, other->bits, other->Size);
}

BitVector::BitVector(BitVector *other) : BitVector(other, other->Size)
{}

BitVector::~BitVector()
{
    free (bits);
}


BitVector::bitref
BitVector::operator[](int x)
{
    return bitref(*this, x);
}

const bool
BitVector::operator[](int x) const
{
    int pos = bitref::bit_pos(x);
    int byte = bitref::byte_index(x);
    return bits[byte] & bitref::mask (pos);
}


BitVector &
BitVector::operator|=(BitVector &x)
{
    for (size_t i = 0; i < Size; i++) {
        bits[i] |= x.bits[i];
    }
    return *this;
}

void
BitVector::ensure (size_t size)
{
    ASSERT (size > Num, "No growth: "<< size <<" <= "<< Num);
    size_t new_size = (size + 7) >> 3;
    if (new_size == Size) return;
    char *old = bits;
    bits = (char*)(calloc (new_size, 1)); // initialized to 0
    if (old) {
        memcpy (bits, old, Size);
        free (old);
    }
    Num = size;
    Size = new_size;
}

void
BitVector::print (llvm::raw_ostream &outs, size_t max)
{
    for (size_t col = 0; col < max; col++) {
        outs << ((*this)[col] ? "1," : "0,");
    }
    outs << "\n";
}

void
BitVector::print (llvm::raw_ostream &outs)
{
    print (outs, Num);
}

BitMatrix::BitMatrix(int init_cols, int init_rows) {
    ColsMax = init_cols;
    RowsMax = init_rows;
    ColSize = RowSize = 0;
    for (int row = 0; row < RowsMax; row++) {
        rows.push_back (new BitVector(ColsMax));
    }
}

BitMatrix::~BitMatrix() {
    for (int row = 0; row < RowsMax; row++) {
        delete rows[row];
    }
}

void
BitMatrix::copy (int row_to, int row)
{
    assert (row_to < RowSize && row < RowSize);
    assert (row_to != row);
    *rows[row_to] |= *rows[row];
}

void
BitMatrix::set (int col, int row)
{
    assert (col < ColSize && row < RowSize);
    rows[row][0][col] = true;
}

bool
BitMatrix::get (int col, int row)
{
    assert (col < ColSize && row < RowSize);
    return rows[row][0][col];
}

void
BitMatrix::ensure (int new_cols, int new_rows)
{
    assert ((new_cols > ColSize && new_rows  > RowSize) ||
            (new_cols > ColSize && new_rows == RowSize) ||
            (new_rows > RowSize && new_cols == ColSize));


//cout << "Size "<< RowSize <<"X"<< ColSize <<" to "<< new_rows <<"X"<< new_cols <<"\n";

    ColSize = new_cols;
    RowSize = new_rows;
    if (new_cols < ColsMax && new_rows < RowsMax)
        return;

    // exponential growth:
    int new_rows2 = (new_rows >= RowsMax ? new_rows * 2 : new_rows );
    int new_cols2 = (new_cols >= ColsMax ? new_cols * 2 : new_cols );

//cout << "Grow "<< RowsMax <<"X"<< ColsMax <<" to "<< new_rows2 <<"X"<< new_cols2 <<"\n";

    // extend columns in existing rows
    if (new_cols2 > ColsMax)
    for (int i = 0; i < RowsMax; i++) {
        rows[i]->ensure(new_cols2);
    }

    // extend rows
    if (new_rows2 > RowsMax)
    for (int i = RowSize; i < new_rows2; i++) {
        rows.push_back (new BitVector(new_cols2));
    }

    ColsMax = new_cols2;
    RowsMax = new_rows2;
}

void
BitMatrix::print (llvm::raw_ostream &outs)
{
    for (int row = 0; row < RowSize; row++) {
        rows[row]->print (outs, ColSize);
    }
    outs << "\n\n";
}

}
