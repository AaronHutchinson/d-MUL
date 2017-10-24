// This program runs the d-dimensional MDDAC algorithm for computing Z-linear
// combinations of points on the Montgomery elliptic curve 25519. Written by
// Aaron Hutchinson, September 2016.
//
// Specifically, the curve is defined over GF(2^255 - 19) by the equation
//                    y^2 = x^3 + 486662x^2 + x
// The algorithm takes advantage of differential addition and doubling formulas
// to provide fast and uniform addition of points. Each iteration of the main
// algorithm (the 'while' loop in Exponentiation below) performs 1 doubling
// and d additions (of curve points).

#include "NTL/ZZ_pXFactoring.h"
#include "NTL/ZZ_pE.h"

#include "NTL/ZZ.h"
#include <NTL/vector.h>
#include <NTL/matrix.h>

#include <utility>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <math.h>
#include <algorithm>
#include <cmath>
#include <unordered_map>
#include <time.h>
#include <Windows.h>

using namespace std;
using namespace NTL;

// Curve constants
#define a NTL::ZZ_p(486662)
#define a2 ZZ_p(973324)

// Global variables to keep counts
int PrecompFieldMult = 0;
int PrecompFieldSquare = 0;
int PrecompFieldAdds = 0;
int PrecompAddCount = 0;
int PrecompDoubleCount = 0;
int FieldMultiplications = 0;
int FieldSquarings = 0;
int FieldAdditions = 0;
int DoubleCount = 0;
int AddCount = 0;
int d = 4;
float T1,T2,T3,T4 = 0.0;

double PCFreq = 0.0;
__int64 CounterStart = 0;

void StartCounter(){
    LARGE_INTEGER li;
    if(!QueryPerformanceFrequency(&li))
	cout << "QueryPerformanceFrequency failed!\n";

    PCFreq = double(li.QuadPart)/1000.0;

    QueryPerformanceCounter(&li);
    CounterStart = li.QuadPart;
}
double GetCounter(){
    LARGE_INTEGER li;
    QueryPerformanceCounter(&li);
    return double(li.QuadPart-CounterStart)/PCFreq;
}


ZZ_p ConvertToAffine (Vec<ZZ_p> P){
    // Returns the affine x-coordinate of the point P, which is input with (X,Z) projective coordinates
    return P[0]*inv(P[1]);
}
Vec<ZZ_p> NormalizeZCoord (Vec<ZZ_p> P){
    // Given a point in projective coordinates, returns the point (still in projective coordinates) with a Z coordinate of 1
    if (P[2] == ZZ_p(0)){return P;}

    ZZ_p Zinv = inv(P[2]);
    P[0] = P[0] * Zinv;
    P[1] = P[1] * Zinv;
    P[2] = ZZ_p(1);
    return P;
}
Vec<ZZ_p> NegatePoint3C( Vec<ZZ_p> Point ){
    // Given P = (X,Y,Z), returns -P = (X,-Y,Z)
    Point[1] = -Point[1];
    return Point;
}
Vec<ZZ_p> DiffDouble (Vec<ZZ_p> P){
    // Differential Doubling formula
    // Field operation counts are: 2 Multiplications, 2 Squarings, 4 Additions, 1 constant multiplication

    if ((P[0] == ZZ_p(0)) && (P[1] == ZZ_p(0))){return P;}

    Vec<ZZ_p> result;
    result.SetLength(2);
    //a24=(a-2)/4
    ZZ_p a24 = conv<ZZ_p>(121666);
    ZZ_p A,AA,B,BB,C;

    A=P[0]+P[1];
    AA=power(A,2);
    B=P[0]-P[1];
    BB=power(B,2);
    C=AA-BB;
    result[0] = AA*BB;
    result[1] = C*(BB+a24*C);

    FieldMultiplications = FieldMultiplications + 2;
    FieldSquarings = FieldSquarings + 2;
    FieldAdditions = FieldAdditions + 4;
    DoubleCount++;
    return result;
}
Vec<ZZ_p> DiffAdd (Vec<ZZ_p> P1, Vec<ZZ_p> P2, Vec<ZZ_p> P3){
    // Add two points using differential add on Montgomery. The two points are P2 and P3, with P1 = P2 - P3
    // Field operation counts are: 4 Multiplications, 2 Squarings, 6 Additions

    Vec<ZZ_p> result;
    result.SetLength(2);
    if ( (P3[0] == ZZ_p(0)) && (P3[1] == ZZ_p(0)) ){return P2;}
    if ( (P2[0] == ZZ_p(0)) && (P2[1] == ZZ_p(0)) ){return P3;}
    if (P2 == P3){return DiffDouble(P2);}

    ZZ_p A,B,C,D,DA,CB;
    A=P2[0]+P2[1];
    B=P2[0]-P2[1];
    C=P3[0]+P3[1];
    D=P3[0]-P3[1];
    DA=D*A;
    CB=C*B;
    result[0] = P1[1]*power((DA+CB),2);
    result[1] = P1[0]*power((DA-CB),2);

    FieldMultiplications = FieldMultiplications + 4;
    FieldSquarings = FieldSquarings + 2;
    FieldAdditions = FieldAdditions + 6;
    AddCount++;
    return result;
}
Vec<ZZ_p> ProjectiveDouble( Vec<ZZ_p> P ){
    // Doubles an elliptic curve point P which is given in projective (X,Y,Z) coordinates and returns 2P in projective (X,Y,Z) coordinates
    // Field operation counts are: 13 Multiplications, 5 Squarings, 8 Additions, 4 constant multiplications

    Vec<ZZ_p> result;
    result.SetLength(3);

    // Check if identity or Y coordinate is 0
    if ( (P[2] == ZZ_p(0) ) || ( P[1] == ZZ_p(0) ) ){
        result[0] = 0;
        result[1] = 1;
        result[2] = 0;
        return result;
    }

    ZZ_p Z2,T,T2,T3,TZ,TZ2,TZ3,C,D,D2,D3;
    Z2 = power(P[2], 2);
    T  = P[1] + P[1];
    T2 = power( T , 2 );
    T3 = T * T2;
    TZ = T * P[2];
    TZ2= power( TZ, 2 );
    TZ3= TZ * TZ2;
    C  = a * P[2] + ZZ_p(2)*P[0];
    D  = 3 * power(P[0], 2) + a2 * P[0] * P[2] + Z2;
    D2 = power( D , 2 );
    D3 = D * D2;

    result[0] = T * ( P[2] * D2 - TZ2 * C );
    result[1] = ( P[0] + C ) * D * P[2] * T2 - D3 - P[1] * TZ2 * T;
    result[2] = TZ3;

    /*
    FieldMultiplications = FieldMultiplications + 13;
    FieldSquarings = FieldSquarings + 5;
    FieldAdditions = FieldAdditions + 8;
    */
    PrecompFieldMult = PrecompFieldMult + 13;
    PrecompFieldSquare = PrecompFieldSquare + 5;
    PrecompFieldAdds = PrecompFieldAdds + 8;
    PrecompDoubleCount = PrecompDoubleCount + 1;
    return result;
}
Vec<ZZ_p> ProjectiveAdd ( Vec<ZZ_p> P1, Vec<ZZ_p> P2 ){
    // Adds two elliptic curve points P1 and P2, which are given in projective (X,Y,Z) coordinates, and returns their sum in projective (X,Y,Z) coordinates
    // Field operation counts are: 15 + 4 Multiplications, 2 Squarings, 8 Additions, 1 constant multiplication
    if ( (P1.length() != 3) || (P2.length() != 3 ) ){
        cout << "Error in ProjectiveAdd! Point has length != 3";
        return P1;
    }

    Vec<ZZ_p> Identity3C;
    Identity3C.SetLength(3);
    Identity3C[0] = ZZ_p(0);
    Identity3C[1] = ZZ_p(1);
    Identity3C[2] = ZZ_p(0);

    // Check if either point is the identity
    if ( P1[2] == ZZ_p(0) ){return P2;}
    if ( P2[2] == ZZ_p(0) ){return P1;}
    // Check if both points are inverses of each other
    if ( NegatePoint3C(P1) == P2 ){return Identity3C;}
    // Check if both points are the same
    if ( (P2[0] * P1[2] == P1[0] * P2[2]) && ( P2[1] * P1[2] == P1[1] * P2[2] ) ){ return DiffDouble(P1); }


    ZZ_p A1,A2,B1,B2,C,Z,M2,M3,N2,N3,ADiff,BDiff;
    A1 = P2[0] * P1[2];
    A2 = P1[0] * P2[2];
    B1 = P1[1] * P2[2];
    B2 = P2[1] * P1[2];
    Z  = P1[2] * P2[2];
    C  = a*Z + A2 + A1;
    ADiff = A1 - A2;
    BDiff = B2 - B1;
    M2 = power( ADiff , 2 );
    M3 = M2 * ( ADiff );
    N2 = power( BDiff , 2 );
    N3 = N2 * ( BDiff );

    Vec<ZZ_p> result;
    result.SetLength(3);
    result[0] = Z * N2 *(ADiff) - M3*C;
    result[1] = (A2 + C)*( BDiff ) * M2 - Z * N3 - B1 * M3;
    result[2] = Z * M3;

    /*
    FieldMultiplications = FieldMultiplications + 19;
    FieldSquarings = FieldSquarings + 2;
    FieldAdditions = FieldAdditions + 8;
    */
    PrecompFieldMult = PrecompFieldMult + 15;
    PrecompFieldSquare = PrecompFieldSquare + 2;
    PrecompFieldAdds = PrecompFieldAdds + 8;
    PrecompAddCount = PrecompAddCount + 1;


    return result;
}
void PrintVecZZp (const Vec<ZZ_p> v){
    // Prints the ZZ_p vector v to cout
    cout << "[" ;
    for (int i = 0; i < v.length() - 1; i++){
        cout << v[i] << ",";
    }
    cout << v[v.length()-1];
    cout<< "]\n";
}
void PrintVecZZ (const Vec<ZZ> v){
    // Prints the ZZ vector v to cout
    cout << "[" ;
    for (int i = 0; i < v.length() - 1; i++){
        cout << v[i] << ",";
    }
    cout << v[v.length()-1];
    cout<< "]\n";
}
void PrintVecOfVecs ( vector< Vec<ZZ_p> > Points){
    // Prints a vector of Vec<ZZ_p>'s to cout
    cout << "Points\n";
    for (int i = 0; i < Points.size()-1; i++ )
    {
        cout << "P" << i << " = ";
        PrintVecZZp(Points[i]);
    }
    cout << "\n";
}
void PrintVecOfVecsAffine( vector< Vec<ZZ_p> > Points){
    // Prints a vector of Vec<ZZ_p>'s in affine coordinates (x-only) to cout
    cout << "Points in affine (there are " << Points.size() << " many):\n";
    for (int i = 0; i < Points.size(); i++ )
    {
        cout << "P" << i << " = ";
        if ((Points[i][0] == ZZ_p(0) )&& (Points[i][1] == ZZ_p(0) )){cout << 0;}
        else{cout << ConvertToAffine(Points[i]); }
        cout << "\n";
    }
    cout << "\n";
}
void PrintMatZZ (Mat<ZZ> A){
    // Prints the matrix A to cout
    cout << "[\n";
    for (int i = 0; i < A.NumRows(); i++)
    {
        cout << "[";
        for (int j = 0; j < A[i].length()-1; j++)
        {
            cout << A[i][j] << ",";
        }
        cout << A[i][A[i].length()-1] << "]\n";
    }
    cout << "]\n";
    return;

}
Vec<ZZ> getInput(){
    // Gets a coefficient vector from the user. This would be the a_i in the linear combination a_0 P_0 + a_1 P_1 + ... a_d P_d
    Vec<ZZ> coef;
    coef.SetLength(d);
    for ( int i = 0; i < d; i++)
    {
        long temp;
        cin >> temp;
        coef[i] = conv<ZZ>(temp);
    }
    return coef;
}
int Weight(Vec<ZZ> P){
    // Returns the Hamming weight of P
    int acc = 0;
    for (int i = 0; i < P.length(); i++)
    {
        if (P[i] != ZZ(0) ){acc++;}
    }
    return acc;
}
int NumberOfOdds(Vec<ZZ> P){
    // Returns the number of odd entries in P
    int acc = 0;
    for (int i = 0; i < P.length(); i++)
    {
        if (P[i] % 2 == 1){acc++;}
    }
    return acc;
}
Mat<ZZ> Initialization(Vec<ZZ> coef){
    // First step of main algorithm. Given a coefficient vector of integers,
    // this function returns a state matrix  having coef as a row.
    // This function is set to 'always subtract' when defining the remaining
    // rows of the matrix, and changes the rows in left to right order (from
    // the perspective of the row coef).

    const int h = NumberOfOdds(coef);
    Mat<ZZ> A;
    A.SetDims(d+1,d);
    A[h] = coef;

    // Find indices for even and odd entries
    vector<int> oddsInCoef,evensInCoef;
    for (int i = 0; i < d; i++)
    {
        if ( coef[i] % 2 == 0 ){ evensInCoef.push_back(i); }
        else { oddsInCoef.push_back(i); }
    }
    // Define rows above A_h
    for (int i = h-1; i >= 0; i-- )
    {
        A[i] = A[i+1];
        A[i][oddsInCoef[h-i-1]]--;
    }
    // Define rows below A_h
    for (int i = h+1; i <= d; i++ )
    {
        A[i] = A[i-1];
        A[i][evensInCoef[i-h-1]]--;
    }
    return A;
}
ZZ Magnitude( Mat<ZZ> A ){
    // Returns the magnitude of the matrix A, which is the maximum of the absolute value of the entries in A
    ZZ MaxOfMatrix = ZZ(0);
    for (int i = 0; i < A.NumRows(); i++ )
    {
        for (int j = 0; j < A.NumCols(); j++ )
        {
            if (A[i][j] > MaxOfMatrix)
                MaxOfMatrix = NTL::abs(A[i][j]);
        }
    }
    return MaxOfMatrix;
}
Mat<ZZ> GetMatrix( Mat<ZZ> A, vector< Vec<ZZ> > &DDiffVec, vector< vector<int> > &DRowSeq ){
    // Second step of the main algorithm. Given a state matrix A, returns a state matrix B whose entries
    // are roughly half that of A. This is called repeatedly in the main algorithm Exponentiation to
    // find a sequence of matrices.

    // DRowSeq stores the two rows of B which add to a given row of A. E.g., DRowSeq[2][0] = 3 and DRowSeq[2][1] = 4
    //      would mean that B_3 + B_4 = A_2
    // DDiffVec stores the differences of the rows of B. These differences are balanced ternary vectors.
    // Following the above example, DDiffVec[2] = [ 1, -1, 0, 1 ] would mean B_3 - B_4 = [ 1, -1, 0, 1 ]

    Mat<ZZ> B;
    B.SetDims(d+1, d);


    // Get sigma
    vector<int> sigma(d);
    for ( int i = 0; i < d; i++)
    {
        Vec<ZZ> temp = A[i+1] - A[i];
        for (int j = 0; j < d; j++)
        {
            if (temp[j] != ZZ(0) )
            {
                sigma[i] = j;
                break;
            }
        }
    }

    // Get c's
    Vec<ZZ> c;
    c.SetLength(d);
    for (int i = 0; i < d; i++ )
    {
        c[i] = A[d][i] - A[0][i];
    }

    Vec<ZZ> HalfFirstRow = A[0];
    for (int i = 0; i < d; i++)
    {
        HalfFirstRow[i] = HalfFirstRow[i] / 2;
    }
    int h = NumberOfOdds(HalfFirstRow);
    int x = h;
    int y = h;

    // Set initial row of B
    B[h] = HalfFirstRow;


    Vec<ZZ> R;
    R.SetLength(d);
    DRowSeq[0][0] = h;
    DRowSeq[0][1] = h;
    DDiffVec[0] = R;
    // Define the remaining rows of B. B[h][i] is alpha[i]
    for (int k = 1; k < d+1; k++)
    {
        Vec<ZZ> temp;
        temp.SetLength(d);
        if ( B[h][ sigma[k-1] ] % 2 == 1 )
        {
            temp[sigma[k-1]] = c[sigma[k-1]];
            B[x-1] = B[x] + temp;
            R = R + temp;
            x--;
        }
        else
        {
            temp[sigma[k-1]] = c[sigma[k-1]];
            B[y+1] = B[y] + temp;
            R = R - temp;
            y++;
        }

        DRowSeq[k][0] = x;
        DRowSeq[k][1] = y;
        DDiffVec[k] = R;

    }
    return B;
}
Vec<ZZ> BalTernVecAddOne( Vec<ZZ> myVector ){
    // Adds one to the balanced ternary vector myVector to get another balanced ternary vector

    myVector[myVector.length() - 1]++;
    for (int i = myVector.length() - 1; i >= 0; i--)
    {
        if (myVector[i] == ZZ(2) )
        {
            myVector[i] = ZZ(-1);
            myVector[i-1]++;
        }
    }
    return myVector;
}
Vec<ZZ> ConvertToBalTern( int n ){
    // Converts the non-negative integer n into a balanced ternary vector
    if (n < 0){cout << "ConvertToBalTern took negative entry!!";}

    int r,q;
    Vec<ZZ> BalTernVec;
    BalTernVec.SetLength(d);

    int counter = 0;
    while (n > 0)
    {
        r = n % 3;
        n = n / 3;
        if ( r == 2 ){
            r = -1;
            n++;
        }
        if (counter > d){
            cout << "Overflow error in ConvertToBalTern!!!";
        }
        BalTernVec[ BalTernVec.length() - counter - 1 ] = ZZ(r);
        counter++;
    }

    return BalTernVec;
}
vector< Vec<ZZ_p> > InitializeMap( Vec<Vec<ZZ_p> > Points ){
    // Takes in d many elliptic curve points **in projective (X,Y,Z)-coordinates** and
    //    outputs all (3^d-1)/2 many {0,1,-1}-linear combinations of them in **(X,Z)-coordinates**
    // This map only computes half of the possible points. The half that it computes are the combinations
    // whose coefficient vector has a leading 1 (so the ternary vectors corresponding to positive integers)

    vector< Vec<ZZ_p> > TernVectorToPointWithY;
    vector< Vec<ZZ_p> > TernVectorToPoint;
    Vec<ZZ> CountingVector;
    CountingVector.SetLength(d);

    Vec<ZZ_p> Identity3C;
    Identity3C.SetLength(3);
    Identity3C[0] = ZZ_p(0);
    Identity3C[1] = ZZ_p(1);
    Identity3C[2] = ZZ_p(0);

    Vec<ZZ_p> Identity2C;
    Identity2C.SetLength(2);
    Identity2C[0] = ZZ_p(0);
    Identity2C[1] = ZZ_p(0);



    TernVectorToPointWithY.push_back( Identity3C );
    TernVectorToPoint.push_back( Identity2C );


    // Populate maps
    for (int i = 1; i <= ( pow(3,d) - 1 )/2; i++ )
    {
        CountingVector = ConvertToBalTern(i);
        Vec<ZZ_p> tempPoint;
        tempPoint.SetLength(3);
        for (int j = 0; j < d; j++)
        {
            if (CountingVector[j] == ZZ(1) )
                {tempPoint = ProjectiveAdd( tempPoint, Points[j] );}
            if (CountingVector[j] == ZZ(-1) )
                {tempPoint = ProjectiveAdd( tempPoint, NegatePoint3C(Points[j]) );}
        }
        TernVectorToPointWithY.push_back( tempPoint );
        TernVectorToPoint.push_back( Identity2C );
        TernVectorToPoint[i][0] = tempPoint[0];
        TernVectorToPoint[i][1] = tempPoint[2];
    }

    return TernVectorToPoint;
}
Vec<ZZ> NegateZZVec( Vec<ZZ> myVector ){
    // Negates a vector of ZZ's by multiplying by -1. This is generally used to find the negative of a balanced ternary vector
    // since InitializeMap only computes points for positive balanced ternary vectors.
    for (int i = 0; i < myVector.length(); i++ )
    {
        myVector[i] = -myVector[i];
    }
    return myVector;
}
int BalTernToInt( Vec<ZZ> BalTernVec ){
    // Converts a balanced ternary vector into it's integer representation. Can return a negative result
    int result = 0;
    int c;
    for ( int i = BalTernVec.length() - 1; i >= 0; i-- ){
        conv(c,BalTernVec[i]);
        result = result + c * pow( 3, int(BalTernVec.length()) - i - 1 );
    }
    return result;
}
void PrintSeqOfMatrix( vector< Mat<ZZ> > A ){
    // Prints each matrix in the sequence of matrices A
    for (int i = 0; i < A.size() ; i++ )
    {
        cout << "A[" << i << "] = \n";
        PrintMatZZ(A[i]);
        cout << "\n";
    }
    return;
}
void PrintMap( vector< Vec<ZZ_p> > TheMap ){
    // Prints the given map, the key value followed by the object stored with that key
    for (int i = 0; i < TheMap.size(); i++ )
    {
        cout << i << " = ";
        PrintVecZZp(TheMap[i]);
        cout << "\n";
    }
}


Vec<ZZ_p> Exponentiation( Vec<ZZ> coef, Vec< Vec<ZZ_p> > Points ){
    // Main MDDAC exponentiation algorithm. Computes the 'dot product' of coef with Points.
    // I.e., if coef = [ a_0, a_1, a_2, a_3 ] and Points = [ P_0, P_1, P_2, P_3 ], then
    // the output will be the point a_0*P_0 + a_1*P_1 + a_2*P_2 + a_3*P_3 in (X,Z) projective coordinates

    // Initialization

    StartCounter();
    vector< Mat<ZZ> > A(1);
    vector< vector< vector<int> > > DRowAddSeq(1, vector< vector<int> >(d+1, vector<int>(2, -1)));
    vector< vector< Vec<ZZ> > > DDiffVec(1, vector< Vec<ZZ> >(d+1));
    A[0] = Initialization(coef);
    int h = NumberOfOdds(coef);
    int k = 0;

    // Main loop
    while ( Magnitude(A[k]) > ZZ(1) )
    {
        if (k != 0)
        {
            DRowAddSeq.push_back( vector< vector<int> >(d+1, vector<int>(2,-1)) );
            DDiffVec.push_back( vector< Vec<ZZ> >(d+1) );
        }
        A.push_back(GetMatrix( A[k], DDiffVec[k], DRowAddSeq[k] ));
        k = k+1;
    }
    T1 = GetCounter();

    //PrintSeqOfMatrix(A);

    // This map holds the correspondence between {0,1,-1}-vectors and combinations of elliptic curve points
    // Points are looked up by the integer represented by the balanced ternary vector

    vector< Vec<ZZ_p> > TernVecToPoints = InitializeMap( Points );
    T2 = GetCounter() - T1;

    // Initialize the Q's
    vector<vector< Vec<ZZ_p> > > Q(k+1 , vector< Vec<ZZ_p> >(d+1) );
    for ( int i = 0; i < d+1; i++)
    {
        Q[k][i].SetLength(2);
        int ARowAsInt = BalTernToInt( A[k][i] );
        if (ARowAsInt >= 0){Q[k][i] = TernVecToPoints[ARowAsInt];}
        if (ARowAsInt <  0){Q[k][i] = NegatePoint3C( TernVecToPoints[-ARowAsInt] );}
    }
    T3 = GetCounter() - T2 - T1;

    k = k-1;
    // Iteratively calculate the rest of the Q's

    while (k >= 0)
    {
        for (int i = 0; i <= d; i++)
        {
            int DiffVecAsInt = BalTernToInt( DDiffVec[k][i] );
            if ( DiffVecAsInt >= 0 ){   Q[k][i] = DiffAdd( TernVecToPoints[DiffVecAsInt]  , Q[k+1][ DRowAddSeq[k][i][0] ]  , Q[k+1][ DRowAddSeq[k][i][1] ] );}
            else{                       Q[k][i] = DiffAdd( TernVecToPoints[-DiffVecAsInt] , Q[k+1][ DRowAddSeq[k][i][1] ]  , Q[k+1][ DRowAddSeq[k][i][0] ] );}
        }
        k = k-1;
    }
    T4 = GetCounter() - T3 - T2 - T1;
    return Q[0][h];

}



int main()
{

    // Set the field
    SetSeed( ZZ(1) );
    ZZ p;
    p=power2_ZZ(255)-ZZ(19);
    ZZ_p::init(conv<ZZ>(p));

    // Set up the points P_i
    Vec< Vec<ZZ_p> > P;
    P.SetLength(8);
    P[0].SetLength(3);
    P[1].SetLength(3);
    P[2].SetLength(3);
    P[3].SetLength(3);
    P[4].SetLength(3);
    P[5].SetLength(3);
    P[6].SetLength(3);
    P[7].SetLength(3);

    // Point declarations
    {
    // Base Point P
    string P0XS = "9";
    string P0YS = "14781619447589544791020593568409986887264606134616475288964881837755586237401";
    string P0ZS = "1";
    ZZ P0X(NTL::INIT_VAL, P0XS.c_str());
    ZZ P0Y(NTL::INIT_VAL, P0YS.c_str());
    ZZ P0Z(NTL::INIT_VAL, P0ZS.c_str());
    P[0][0] = conv<ZZ_p>(P0X);
    P[0][1] = conv<ZZ_p>(P0Y);
    P[0][2] = conv<ZZ_p>(P0Z);

    // 1025 * P
    string P1XS = "3022554069703705475639174349313591763256900032963361100611665406392770655907";
    string P1YS = "6443465753987354357357698393644934350755095543763529530369326071229119094686";
    string P1ZS = "1";
    ZZ P1X(NTL::INIT_VAL, P1XS.c_str());
    ZZ P1Y(NTL::INIT_VAL, P1YS.c_str());
    ZZ P1Z(NTL::INIT_VAL, P1ZS.c_str());
    P[1][0] = conv<ZZ_p>(P1X);
    P[1][1] = conv<ZZ_p>(P1Y);
    P[1][2] = conv<ZZ_p>(P1Z);

    // 4258 * P
    string P2XS = "54768532575421380092858199436648431379977496790326727505097502885908939223422";
    string P2YS = "2063734120558115050010968694798849684436241344541802115609436389418445990781";
    string P2ZS = "1";
    ZZ P2X(NTL::INIT_VAL, P2XS.c_str());
    ZZ P2Y(NTL::INIT_VAL, P2YS.c_str());
    ZZ P2Z(NTL::INIT_VAL, P2ZS.c_str());
    P[2][0] = conv<ZZ_p>(P2X);
    P[2][1] = conv<ZZ_p>(P2Y);
    P[2][2] = conv<ZZ_p>(P2Z);

    // 3498 * P
    string P3XS = "26203917327795801069901763606138435614272233824482330788343431722654358149135";
    string P3YS = "328817272653981528622928089311796991549039109546548698393045828136621798705";
    string P3ZS = "1";
    ZZ P3X(NTL::INIT_VAL, P3XS.c_str());
    ZZ P3Y(NTL::INIT_VAL, P3YS.c_str());
    ZZ P3Z(NTL::INIT_VAL, P3ZS.c_str());
    P[3][0] = conv<ZZ_p>(P3X);
    P[3][1] = conv<ZZ_p>(P3Y);
    P[3][2] = conv<ZZ_p>(P3Z);

    // 44587 * P
    string P4XS = "5006531462789316172978808054639437619381540614276233670508736270530195780215";
    string P4YS = "36579225922588334312759061462817434086924863505190566713152364559108092783617";
    string P4ZS = "1";
    ZZ P4X(NTL::INIT_VAL, P4XS.c_str());
    ZZ P4Y(NTL::INIT_VAL, P4YS.c_str());
    ZZ P4Z(NTL::INIT_VAL, P4ZS.c_str());
    P[4][0] = conv<ZZ_p>(P4X);
    P[4][1] = conv<ZZ_p>(P4Y);
    P[4][2] = conv<ZZ_p>(P4Z);

    // 971 * P
    string P5XS = "38536016481012089794601238669934429265559638052142054476708166748390632434904";
    string P5YS = "22510506515929525609205301905383006336324589812293521519998283641796320274175";
    string P5ZS = "1";
    ZZ P5X(NTL::INIT_VAL, P5XS.c_str());
    ZZ P5Y(NTL::INIT_VAL, P5YS.c_str());
    ZZ P5Z(NTL::INIT_VAL, P5ZS.c_str());
    P[5][0] = conv<ZZ_p>(P5X);
    P[5][1] = conv<ZZ_p>(P5Y);
    P[5][2] = conv<ZZ_p>(P5Z);

    // 19601 * P
    string P6XS = "26970451130374359698971658514102732048792261588348089432299943888683469403835";
    string P6YS = "29789381732665397468472703528889969406124523047186297253203621113948750362082";
    string P6ZS = "1";
    ZZ P6X(NTL::INIT_VAL, P6XS.c_str());
    ZZ P6Y(NTL::INIT_VAL, P6YS.c_str());
    ZZ P6Z(NTL::INIT_VAL, P6ZS.c_str());
    P[6][0] = conv<ZZ_p>(P6X);
    P[6][1] = conv<ZZ_p>(P6Y);
    P[6][2] = conv<ZZ_p>(P6Z);

    // 12419 * P
    string P7XS = "32559898633315891331312514705752453885037175053969076472426698935319846438025";
    string P7YS = "33003279357423646722166618813618749988804443774617280914836149466756821878626";
    string P7ZS = "1";
    ZZ P7X(NTL::INIT_VAL, P7XS.c_str());
    ZZ P7Y(NTL::INIT_VAL, P7YS.c_str());
    ZZ P7Z(NTL::INIT_VAL, P7ZS.c_str());
    P[7][0] = conv<ZZ_p>(P7X);
    P[7][1] = conv<ZZ_p>(P7Y);
    P[7][2] = conv<ZZ_p>(P7Z);
    }
    /*
    cout << "P0 = ";
    PrintVecZZp( P[0] );

    cout << "\nP1 = ";
    PrintVecZZp( P[1] );

    cout << "\nP2 = ";
    PrintVecZZp( P[2] );

    cout << "\nP3 = ";
    PrintVecZZp( P[3] );
    cout << "\n----------------------------------------------------------------------\n";
    */

    Vec<ZZ> coef;
    coef.SetLength(8);
    RandomBits(coef[0] , 64);
    RandomBits(coef[1] , 64);
    RandomBits(coef[2] , 64);
    RandomBits(coef[3] , 64);
    RandomBits(coef[4] , 32);
    RandomBits(coef[5] , 32);
    RandomBits(coef[6] , 32);
    RandomBits(coef[7] , 32);
    Vec<Vec<ZZ_p> > Q;
    Q.SetLength(4);
    Q[0].SetLength(3);
    Q[0] = P[0];
    Q[1].SetLength(3);
    Q[1] = P[1];
    Q[2].SetLength(3);
    Q[2] = P[2];
    Q[3].SetLength(3);
    Q[3] = P[3];
    /*Q[4].SetLength(3);
    Q[4] = P[4];
    Q[5].SetLength(3);
    Q[5] = P[5];
    Q[6].SetLength(3);
    Q[6] = P[6];
    Q[7].SetLength(3);
    Q[7] = P[7];
    */
    Vec<ZZ> b;
    b.SetLength(4);
    b[0] = coef[0];
    b[1] = coef[1];
    b[2] = coef[2];
    b[3] = coef[3];
    /*
    b[4] = coef[4];
    b[5] = coef[5];
    b[6] = coef[6];
    b[7] = coef[7];
    */
    //cout << "Computing " << coef[0] << " * P0 + " << coef[1] << " * P1 + " << coef[2] << " * P2 + " << coef[3] << " * P3 ... \n\n";


    Exponentiation( b, Q );
    int n = 64;
    /*
    cout << "d = " << d << " ( bit coefficients):\nField operation counts:\n   Precomputation:\n   "
        << PrecompFieldMult << " multiplications\n   "
        << PrecompFieldSquare << " squarings\n   "
        << PrecompFieldAdds << " additions\n   "
        << PrecompAddCount << " points added projectively\n   "
        << PrecompTime << " time taken on precomputation (seconds)\n\n   Main loop:\n   "
        << FieldMultiplications << " multiplications\n   "
        << FieldSquarings << " squarings\n   "
        << FieldAdditions << " additions\n   "
        << DoubleCount << " points doubled differentially\n   "
        << AddCount << " points added differentially\n   "
        << t << " time taken in main loop (seconds)\n\n   "
        << t + PrecompTime << " time taken total\n\n";
    */
    cout << "\nTiming analysis (seconds):\n"
        << "T1( Edwards, " << n << ", " << d << ") = " << T1/1000.0 << "\n"
        << "T2( Edwards, " << n << ", " << d << ") = " << T2/1000.0 << "\n"
        << "T3( Edwards, " << n << ", " << d << ") = " << T3/1000.0 << "\n"
        << "T4( Edwards, " << n << ", " << d << ") = " << T4/1000.0 << "\n"
        << "Total time: " << (T1 + T2 + T3 + T4)/1000.0 << "\n\n"
        << "T1/(T3 + T4) = " << (T1 / (T3 + T4)) << "\n"
        << "(T1 + T3)/T4 = " << ((T1 + T3)/T4) << "\n\n";


}
