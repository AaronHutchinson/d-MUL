/* This program runs the d-MUL algorithm on the Twisted Edwards curve FourQ.
   Specifically, FourQ is a curve defined over GL(p^2), where p = 2^127 - 1 and
   the field is constructed using the polynomial X^2 + 1.
   The program offers translating between the Twisted Edwards curve and its birationally
   equivalent Weierstrauss curve, where the mapping is given by composing the equivalences
   between Twisted Edwards <-> Montgomery <-> Weierstrauss.
   The Twisted Edwards curve is defined by a*x^2 + y^2 = 1 + d*x^2*y^2, where
      a = -1, d = 4205857648805777768770 + 125317048443780598345676279555970305165*X
   The Weierstrauss curve is defined by y^2 = x^3 + alpha*x + beta, where
      alpha = (a-d)^2 / 16 - (a+d)^2 / 12   ,    beta = (a+d)^3 / 108 - (a+d)(a-d)^2 / 96
   The birational mapping is given by phi: Weierstrauss -> Edwards, phi(u,v) = (x,y), where
         x = u/v - A/(3*B*v)
         y = (3*B*u - A - 3)/(3*B*u - A + 3)
      and A = 2(a+d)/(a-d) and B = 4/(a-d) are field constants.
*/
#include "NTL/ZZ_pXFactoring.h"
#include <NTL/vector.h>
#include <NTL/matrix.h>
#include "NTL/ZZ.h"
#include "NTL/ZZ_p.h"
#include <NTL/ZZ_pX.h>
#include <NTL/ZZ_pEX.h>
#include <iostream>
#include <vector>
#include <time.h>
#include <Windows.h>

using namespace std;
using namespace NTL;

// Curve coefficients for the Twisted Edwards curve and the birationally equivalent Weierstrauss curve
ZZ_pE EdwardsA, EdwardsD, WeierA, WeierB;
// Finite field polynomial: X^2 + 1
ZZ_pX PolyModulus;

// Lookup tables for algorithm
const vector<int> RowIncrements{1,-1,-1,1};
const vector<int> IndexChoices{1,0,1,0};
const vector<int> IndexIncrements{1,-1,1,-1};

// Global timing variables
float T1, T2, T3, T4 = 0;
double PCFreq = 0.0;
__int64 CounterStart = 0;

// Weierstrauss curve structure functions
struct WeierAff{
    // Structure for Weierstrauss affine coordinates
    ZZ_pE x;
    ZZ_pE y;

    WeierAff operator-() const{
        WeierAff P;
        P.x = x;
        P.y = -y;
        return P;
    }
};
struct WeierProj{
    // Structure for Weiersrauss projective coordinates
    ZZ_pE x;
    ZZ_pE y;
    ZZ_pE z;

    // Weierstrauss curve negation is given by negating the second coordinate
    WeierProj operator-() const{
        WeierProj P;
        P.x = x;
        P.y = -y;
        P.z = z;
        return P;
    }
};
bool operator==(const WeierProj P, const WeierProj Q ){
    // Two projective points are equal if and only if the two equalities below hold
    return ( (P.x * Q.y == P.y * Q.x) && (P.y * Q.z == P.z * Q.y) );
}
bool operator==(const WeierAff P, const WeierAff Q ){
    // Two projective points are equal if and only if the two equalities below hold
    return ( (P.x == Q.x) && (P.y == Q.y) );
}
WeierAff WeierAffIdentity(){
    // Returns the affine identity for Weierstrauss curves. In theory, this is the 'point at infinity', and so is implemented as the point (0,0), which is not on the curve
    WeierAff P;
    P.x = 0;
    P.y = 0;
    return P;
}
WeierProj WeierProjIdentity(){
    // Returns the projective identity for Weierstruass curve
    WeierProj P;
    P.x = 0;
    P.y = 1;
    P.z = 0;
    return P;
}
WeierAff ProjToAff(const WeierProj &P){
    // Conversion from projective coordinates to affine coordinates. Works for Weierstrauss or Edwards points
    if (P == WeierProjIdentity()){return WeierAffIdentity();}
    WeierAff Q;
    Q.x = P.x / P.z;
    Q.y = P.y / P.z;
    return Q;
}
WeierProj AffToProj(const WeierAff &P){
    // Conversion from affine to projective coordinates. Works for Weierstrauss or Edwards points
    if (P == WeierAffIdentity()){return WeierProjIdentity();}
    WeierProj Q;
    Q.x = P.x;
    Q.y = P.y;
    Q.z = ZZ_pE(1);
    return Q;
}

// Edwards curve structure functions
struct EdwardsAff{
    // Structure for Edwards affine coordinates
    ZZ_pE x;
    ZZ_pE y;

    // Edwards curve negation is given by negating the first coordinate
    EdwardsAff operator-() const{
        EdwardsAff P;
        P.x = -x;
        P.y = y;
        return P;
    }
};
struct EdwardsProj{
    // Structure for Edwards projective coordinates
    ZZ_pE x;
    ZZ_pE y;
    ZZ_pE z;

    // Edwards curve negation is given by negating the first coordinate
    EdwardsProj operator-() const{
        EdwardsProj P;
        P.x = -x;
        P.y = y;
        P.z = z;
        return P;
    }
};
bool operator==(const EdwardsProj P, const EdwardsProj Q ){
    // Two projective points are equal if and only if the two equalities below hold
    return ( (P.x * Q.y == P.y * Q.x) && (P.y * Q.z == P.z * Q.y) );
}
bool operator==(const EdwardsAff P, const EdwardsAff Q ){
    // Two projective points are equal if and only if the two equalities below hold
    return ( (P.x == Q.x) && (P.y == Q.y) );
}
EdwardsAff EdwardsAffIdentity(){
    // Returns the Edwards affine identity point
    EdwardsAff P;
    P.x = 0;
    P.y = 1;
    return P;
}
EdwardsProj EdwardsProjIdentity(){
    // Returns the Edwards projective identity point
    EdwardsProj P;
    P.x = 0;
    P.y = 1;
    P.z = 1;
    return P;
}
EdwardsAff ProjToAff(const EdwardsProj &P){
    // Conversion from projective coordinates to affine coordinates. Works for Weierstrauss or Edwards points
    if (P == EdwardsProjIdentity()){return EdwardsAffIdentity();}
    EdwardsAff Q;
    Q.x = P.x / P.z;
    Q.y = P.y / P.z;
    return Q;
}
EdwardsProj AffToProj(const EdwardsAff &P){
    // Conversion from affine to projective coordinates. Works for Weierstrauss or Edwards points
    if (P == EdwardsAffIdentity()){return EdwardsProjIdentity();}
    EdwardsProj Q;
    Q.x = P.x;
    Q.y = P.y;
    Q.z = ZZ_pE(1);
    return Q;
}
EdwardsProj ProjDouble( const EdwardsProj &P){
    /* Projective doubling formula for Edwards curve. Taken from the following webpage:
            http://hyperelliptic.org/EFD/g1p/auto-twisted-projective.html#doubling-dbl-2008-bbjlp
    */

    // Check if the point is the identity
    if (P == EdwardsProjIdentity()){return P;}

    EdwardsProj Q;
    ZZ_pE B,C,D,E,F,H,J;
    B = power(P.x + P.y, 2);
    C = power(P.x, 2);
    D = power(P.y, 2);
    E = EdwardsA * C;
    F = E+D;
    H = power(P.z, 2);
    J = F-2*H;
    Q.x = (B-C-D) * J;
    Q.y = F * (E-D);
    Q.z = F * J;
    return Q;
}
EdwardsProj ProjAdd( const EdwardsProj &P1, const EdwardsProj &P2){
    /* Projective addition formula for Edwards curve. Taken from the following webpage:
            http://hyperelliptic.org/EFD/g1p/auto-twisted-projective.html#addition-add-2008-bbjlp
    */

    // Check if the points are equal, or if either is the identity
    if (P1 == P2){return ProjDouble(P1);}
    if (P1 == EdwardsProjIdentity()){return P2;}
    if (P2 == EdwardsProjIdentity()){return P1;}
    if (P1 == (-P2)){return EdwardsProjIdentity();}

    EdwardsProj P3;
    ZZ_pE A,B,C,D,E,F,G,H,I,J,K;
    A = P1.z * P2.z;
    B = power(A,2);
    C = P1.x * P2.x;
    D = P1.y * P2.y;
    E = EdwardsD * C * D;
    F = B-E;
    G = B+E;
    H = A * F;
    I = (P1.x + P1.y)*(P2.x + P2.y);
    K = A * G;
    P3.x = H * (I - C - D);
    P3.y = K * (D - EdwardsA * C);
    P3.z = F * G;
    return P3;
}


// Birational equivalence (translation between two curves)
WeierAff EdwardsToWeierAff( const EdwardsAff &P ){
    // Check if P is the identity
    if (P.x == ZZ_pE(0) && P.y == ZZ_pE(1)){return WeierAffIdentity();}

    // Formulas given by the birational equivalence
    WeierAff Q;
    Q.x = ((ZZ_pE(1)+P.y)/(ZZ_pE(1)-P.y))*((EdwardsA - EdwardsD)/ZZ_pE(4)) + (EdwardsA + EdwardsD) / ZZ_pE(6);
    Q.y = ((EdwardsA - EdwardsD)*(ZZ_pE(1) + P.y))/( (ZZ_pE(4)*P.x)*(ZZ_pE(1) - P.y)  );
    return Q;
}
EdwardsAff WeierToEdwardsAff( const WeierAff &P){
    // Check if P is the Weierstrauss identity
    if (P == WeierAffIdentity()){return EdwardsAffIdentity();}

    // Formulas given by the birational equivalence
    EdwardsAff Q;
    Q.x = P.x / P.y - WeierA / (ZZ_pE(3)*WeierB*P.y);
    Q.y = (ZZ_pE(3)*WeierB*P.x - WeierA - ZZ_pE(3)) / (ZZ_pE(3)*WeierB*P.x - WeierA + ZZ_pE(3));
    return Q;
}

// Output/printing functions
void PrintVecZZ (const Vec<ZZ> v){
    // Prints the ZZ vector v to cout
    cout << "[" ;
    for (int i = 0; i < v.length() - 1; i++){
        cout << v[i] << ",";
    }
    cout << v[v.length()-1];
    cout<< "]\n";
}
void PrintMatZZ (const Mat<ZZ> A){
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
void PrintProj(const EdwardsProj &P){
    // Prints a projective point for either Edwards or Weierstrauss coordinates
    cout << "[\n   x = ";
    if (deg(rep(P.x)) == 1){
        cout << rep(P.x)[1] << " * i + ";
    }
    cout << rep(P.x)[0] << "\n   y = ";
    if (deg(rep(P.y)) == 1){
        cout << rep(P.y)[1] << " * i + ";
    }
    cout << rep(P.y)[0] << "\n   z = ";
    if (deg(rep(P.z)) == 1){
        cout << rep(P.z)[1] << " * i + ";
    }
    cout << rep(P.z)[0] << "\n]\n";
}
void PrintProj(const WeierProj &P){
    // Prints a projective point for either Edwards or Weierstrauss coordinates
    cout << "[\n   x = ";
    if (deg(rep(P.x)) == 1){
        cout << rep(P.x)[1] << " * i + ";
    }
    cout << rep(P.x)[0] << "\n   y = ";
    if (deg(rep(P.y)) == 1){
        cout << rep(P.y)[1] << " * i + ";
    }
    cout << rep(P.y)[0] << "\n   z = ";
    if (deg(rep(P.z)) == 1){
        cout << rep(P.z)[1] << " * i + ";
    }
    cout << rep(P.z)[0] << "\n]\n";
}
void PrintAff(const WeierAff &P){
    // Prints an affine point for either Edwards or Weierstrauss coordinates
    if (P.x == 0 && P.y == 0){
        cout << "Identity";
        return;
    }
    cout << "[\n   x = ";
    if (deg(rep(P.x)) == 1){
        cout << rep(P.x)[1] << " * i + ";
    }
    cout << rep(P.x)[0] << "\n   y = ";
    if (deg(rep(P.y)) == 1){
        cout << rep(P.y)[1] << " * i + ";
    }
    cout << rep(P.y)[0] << "\n]\n";
}
void PrintAff(const EdwardsAff &P){
    // Prints an affine point for either Edwards or Weierstrauss coordinates
    cout << "[\n   x = ";
    if (deg(rep(P.x)) == 1){
        cout << rep(P.x)[1] << " * i + ";
    }
    cout << rep(P.x)[0] << "\n   y = ";
    if (deg(rep(P.y)) == 1){
        cout << rep(P.y)[1] << " * i + ";
    }
    cout << rep(P.y)[0] << "\n]\n";
}

// Timing functions
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

// Algorithm functions
vector<long> LastTwoBits(const ZZ &a ){
    // Returns the least two significant bits of a, with placeBitsHere[0] being the least
    //   significant, and placeBitsHere[1] being the second least significant
    vector<long> placeBitsHere{0,0};
    placeBitsHere[0] = a % 2;
    placeBitsHere[1] = ( (a - a % 2) % 4 ) / 2;
    return placeBitsHere;
}
void Initialize( const Vec<ZZ> &coefficients, Mat<ZZ> &A ){
    // Initializes a state matrix from a vector of ZZs
    int d = coefficients.length();
    int h = 0;
    for (int i = 0; i<d; i++){h += coefficients[i] % 2;}
    A[h] = coefficients;

    int UpIndex = h;
    int DownIndex = h;

    // Assigns row h of A to be coefficients, where h is the number of odd entries in coefficients.
    // Defines new rows of A by iterating across coefficients (left to right).
    //      When an even entry is found, a new row is defined on the bottom of A by subtracting one from the even entry.
    //      When an odd entry is found, a new row is defined on the top of A by subtracting one from the odd entry.
    // e.g.:    [       ]       [       ]       [ 2 4 4 ]       [ 2 4 4 ]
    //          [       ]  -->  [ 2 5 4 ]  -->  [ 2 5 4 ]  -->  [ 2 5 4 ]
    //          [ 3 5 4 ]       [ 3 5 4 ]       [ 3 5 4 ]       [ 3 5 4 ]
    //          [       ]       [       ]       [       ]       [ 3 5 3 ]

    for (int i = 0; i<d; i++)
    {
        if ((A[h][i] % 2) == 1)
        {
            A[UpIndex - 1] = A[UpIndex];
            A[UpIndex - 1][i]--;
            UpIndex--;
        }
        else
        {
            A[DownIndex+1] = A[DownIndex];
            A[DownIndex+1][i]--;
            DownIndex++;
        }
    }
}
void DetermineSigma( const Mat<ZZ> &A, vector<int> &Sigma ){
    // Computes the sigma for the matrix A. Sigma[i] is defined as the non-zero entry in the row vector A[i+1] - A[i]
    int d = A.NumCols();
    for (int i = 0; i<d; i++){
        int temp = 0;
        for (int j = 0; j<d; j++){
            temp += j*((( A[i][j] % 2 ) + (A[i+1][j] % 2)) % 2 );
        }
        Sigma.push_back(temp);
    }
}
void DetermineChar( const Mat<ZZ> &A, vector<int> &CharSeq ){
    // Computes the characteristic sequence for the matrix A. This will be used with
    //       the lookup tables above to determine the next matrix in the sequence
    int d = A.NumCols();
    for (int i = 0; i<d; i++){
        CharSeq.push_back((LastTwoBits(A[0][i]))[1] + 2*(LastTwoBits(A[d][i]))[1]);
    }
}
void NextMatrix( const Mat<ZZ> &A, Mat<ZZ> &B, vector< vector<int> > &RowAddSeq /*, vector<Vec<ZZ> > &RowDiff*/ ){
    // Uses A to compute the next matrix B in the sequence. The row addition information is stored in RowAddSeq.
    //      Every row of A should be the sum of two rows from B, and the two rows of B adding to the i'th row of A are stored in RowAddSeq[i]
    int d = A.NumCols();
    int h = 0;
    for (int i = 0; i<d; i++){h+=LastTwoBits(A[0][i])[1];}
    for (int i = 0; i<d; i++){B[h][i] = A[0][i] / 2;}
    RowAddSeq.push_back({h,h});


    vector<int> Sigma;
    vector<int> CharSeq;
    DetermineSigma(A, Sigma);
    DetermineChar(A, CharSeq);

    for (int i = 0; i<d; i++){
        // For readability, we define new variables to store the values from the lookup tables for use in the end computations
        int si = Sigma[i];
        int c = CharSeq[si];
        int ind = IndexChoices[c];
        int indInc = IndexIncrements[c];
        int rowInc = RowIncrements[c];

        // Define the new rows of B and append the information to the row addition sequence
        B[RowAddSeq[i][ind] + indInc] = B[RowAddSeq[i][ind]];
        B[RowAddSeq[i][ind] + indInc][si] += rowInc;
        RowAddSeq.push_back(RowAddSeq[i]);
        RowAddSeq[i+1][ind] += indInc;
    }
}
EdwardsProj Exponentiation( const Vec<ZZ> &coef, const Vec< EdwardsProj > &Points ){

    // Initialization
    int d = coef.length();
    vector< Mat<ZZ> > A(1);
    A[0].SetDims(d+1,d);
    vector< vector< vector<int> > > DRowAddSeq(1, vector< vector<int> >());
    //vector< vector< Vec<ZZ> > > DDiffVec(1, vector< Vec<ZZ> >(d+1));

    StartCounter();
    Initialize(coef, A[0] );
    int k = 0;

    Vec<ZZ> ZeroVec;
    ZeroVec.SetLength(d);

    // Main loop
    while ( A[k][0] != ZeroVec )
    {
        A.push_back(Mat<ZZ>());
        A[k+1].SetDims(d+1,d);
        NextMatrix( A[k], A[k+1], DRowAddSeq[k] );
        DRowAddSeq.push_back( vector< vector<int> >() );
        k = k+1;
    }
    T1 = GetCounter();

    // Initialize the Q's
    vector<vector< EdwardsProj > > Q(k+1 , vector< EdwardsProj >(d+1) );

    // The sigma for the last 0/1 matrix is needed to initialize the Q's. The initial Q's are sums of entries in Points
    vector<int> LastSigma;
    DetermineSigma(A[k], LastSigma);
    Q[k][0] = EdwardsProjIdentity();
    Q[k][1] = Points[LastSigma[0]];
    for ( int i = 2; i < d+1; i++)
    {
        Q[k][i] = ProjAdd( Q[k][i-1], Points[LastSigma[i-1]] );
    }
    k = k-1;

    T3 = GetCounter() - T1;

    // Iteratively calculate the rest of the Q's, as per the algorithm
    while (k >= 0)
    {
        Q[k][0] = ProjDouble(Q[k+1][DRowAddSeq[k][0][0]]);
        for (int i = 0; i < d+1; i++)
        {
            Q[k][i] = ProjAdd( Q[k+1][DRowAddSeq[k][i][0]]  , Q[k+1][ DRowAddSeq[k][i][1] ] );
        }
        k = k-1;
    }
    T4 = GetCounter() - T3 - T1;

    int h=0;
    for (int i = 0; i<d; i++){h += coef[i] % 2;}
    return Q[0][h];

}



int main()
{
    SetSeed( ZZ(1) );

    // Field Setup
    ZZ p = power2_ZZ(127)-ZZ(1);
    ZZ_p::init(conv<ZZ>(p));
    SetCoeff(PolyModulus,0,ZZ_p(1));
    SetCoeff(PolyModulus,1,ZZ_p(0));
    SetCoeff(PolyModulus,2,ZZ_p(1));
    ZZ_pE::init(PolyModulus);

    // Curve coefficients
    string temp0 = "4205857648805777768770";
    string temp1 = "125317048443780598345676279555970305165";
    ZZ temp0ZZ(NTL::INIT_VAL, temp0.c_str());
    ZZ temp1ZZ(NTL::INIT_VAL, temp1.c_str());
    ZZ_pX temp;
    SetCoeff(temp,0,conv<ZZ_p>(temp0ZZ));
    SetCoeff(temp,1,conv<ZZ_p>(temp1ZZ));
    EdwardsD = conv<ZZ_pE>(temp);
    SetCoeff(temp, 0,ZZ_p(-1));
    SetCoeff(temp, 1,ZZ_p(0));
    EdwardsA = conv<ZZ_pE>(temp);
    WeierA = ZZ_pE(2) * (EdwardsA + EdwardsD) / (EdwardsA - EdwardsD);
    WeierB = ZZ_pE(4) / (EdwardsA - EdwardsD);

    // n is bit size of coefficients, d is dimension (number of points)
    int n = 64;
    int d = 4;

    // Choose random coefficients
    Vec<ZZ> coef;
    coef.SetLength(d);
    for (int i = 0; i<d; i++){RandomBits(coef[i],n);}


    // Define points over Weierstrauss curve and map them over to Edwards (for ease of Magma checking)
    Vec<WeierProj> Points;
    Points.SetLength(d);
    Vec<EdwardsProj> EdwardsPoints;
    EdwardsPoints.SetLength(d);
    {

    // P[0] and P[1] were chosen as the two points with and x coordinate of 2
    string P0X0S = "2";
    string P0X1S = "0";
    string P0Y0S = "60576157212191193265710426129961220764";
    string P0Y1S = "36756707731234389776398637038780957812";
    string P0Z0S = "1";
    string P0Z1S = "0";
    ZZ P0X0(NTL::INIT_VAL, P0X0S.c_str());
    ZZ P0X1(NTL::INIT_VAL, P0X1S.c_str());
    ZZ P0Y0(NTL::INIT_VAL, P0Y0S.c_str());
    ZZ P0Y1(NTL::INIT_VAL, P0Y1S.c_str());
    ZZ P0Z0(NTL::INIT_VAL, P0Z0S.c_str());
    ZZ P0Z1(NTL::INIT_VAL, P0Z1S.c_str());
    SetCoeff(temp,0,conv<ZZ_p>(P0X0));
    SetCoeff(temp,1,conv<ZZ_p>(P0X1));
    Points[0].x = conv<ZZ_pE>(temp);
    SetCoeff(temp,0,conv<ZZ_p>(P0Y0));
    SetCoeff(temp,1,conv<ZZ_p>(P0Y1));
    Points[0].y = conv<ZZ_pE>(temp);
    SetCoeff(temp,0,conv<ZZ_p>(P0Z0));
    SetCoeff(temp,1,conv<ZZ_p>(P0Z1));
    Points[0].z = conv<ZZ_pE>(temp);

    string P1X0S = "2";
    string P1X1S = "0";
    string P1Y0S = "109565026248278038465976877585922884963";
    string P1Y1S = "133384475729234841955288666677103147915";
    string P1Z0S = "1";
    string P1Z1S = "0";
    ZZ P1X0(NTL::INIT_VAL, P1X0S.c_str());
    ZZ P1X1(NTL::INIT_VAL, P1X1S.c_str());
    ZZ P1Y0(NTL::INIT_VAL, P1Y0S.c_str());
    ZZ P1Y1(NTL::INIT_VAL, P1Y1S.c_str());
    ZZ P1Z0(NTL::INIT_VAL, P1Z0S.c_str());
    ZZ P1Z1(NTL::INIT_VAL, P1Z1S.c_str());
    SetCoeff(temp,0,conv<ZZ_p>(P1X0));
    SetCoeff(temp,1,conv<ZZ_p>(P1X1));
    Points[1].x = conv<ZZ_pE>(temp);
    SetCoeff(temp,0,conv<ZZ_p>(P1Y0));
    SetCoeff(temp,1,conv<ZZ_p>(P1Y1));
    Points[1].y = conv<ZZ_pE>(temp);
    SetCoeff(temp,0,conv<ZZ_p>(P1Z0));
    SetCoeff(temp,1,conv<ZZ_p>(P1Z1));
    Points[1].z = conv<ZZ_pE>(temp);

    // P[2] = 2000*P[0]
    string P2X0S = "86699439889334972775893318651700205480";
    string P2X1S = "169692589500544726392680388788952774601";
    string P2Y0S = "81398525742275711267137924603487240626";
    string P2Y1S = "156812264340710543367856219193094720039";
    string P2Z0S = "1";
    string P2Z1S = "0";
    ZZ P2X0(NTL::INIT_VAL, P2X0S.c_str());
    ZZ P2X1(NTL::INIT_VAL, P2X1S.c_str());
    ZZ P2Y0(NTL::INIT_VAL, P2Y0S.c_str());
    ZZ P2Y1(NTL::INIT_VAL, P2Y1S.c_str());
    ZZ P2Z0(NTL::INIT_VAL, P2Z0S.c_str());
    ZZ P2Z1(NTL::INIT_VAL, P2Z1S.c_str());
    SetCoeff(temp,0,conv<ZZ_p>(P2X0));
    SetCoeff(temp,1,conv<ZZ_p>(P2X1));
    Points[2].x = conv<ZZ_pE>(temp);
    SetCoeff(temp,0,conv<ZZ_p>(P2Y0));
    SetCoeff(temp,1,conv<ZZ_p>(P2Y1));
    Points[2].y = conv<ZZ_pE>(temp);
    SetCoeff(temp,0,conv<ZZ_p>(P2Z0));
    SetCoeff(temp,1,conv<ZZ_p>(P2Z1));
    Points[2].z = conv<ZZ_pE>(temp);

    // P[3] = 10,000*P[0]
    string P3X0S = "168737199266017511567515093570613851905";
    string P3X1S = "81852340745783594077082063596477788486";
    string P3Y0S = "20654787695570979758295363510591862816";
    string P3Y1S = "86250488983220642057457578626229864840";
    string P3Z0S = "1";
    string P3Z1S = "0";
    ZZ P3X0(NTL::INIT_VAL, P3X0S.c_str());
    ZZ P3X1(NTL::INIT_VAL, P3X1S.c_str());
    ZZ P3Y0(NTL::INIT_VAL, P3Y0S.c_str());
    ZZ P3Y1(NTL::INIT_VAL, P3Y1S.c_str());
    ZZ P3Z0(NTL::INIT_VAL, P3Z0S.c_str());
    ZZ P3Z1(NTL::INIT_VAL, P3Z1S.c_str());
    SetCoeff(temp,0,conv<ZZ_p>(P3X0));
    SetCoeff(temp,1,conv<ZZ_p>(P3X1));
    Points[3].x = conv<ZZ_pE>(temp);
    SetCoeff(temp,0,conv<ZZ_p>(P3Y0));
    SetCoeff(temp,1,conv<ZZ_p>(P3Y1));
    Points[3].y = conv<ZZ_pE>(temp);
    SetCoeff(temp,0,conv<ZZ_p>(P3Z0));
    SetCoeff(temp,1,conv<ZZ_p>(P3Z1));
    Points[3].z = conv<ZZ_pE>(temp);

    for (int i = 0; i < d; i++ ){EdwardsPoints[i] = AffToProj(WeierToEdwardsAff(ProjToAff(Points[i])));}

    }


    // Print the points
    cout << "Current points (in Weierstrauss form) are:\n";
    for (int i = 0; i<d; i++){
        cout << "P[" << i+1 << "] =\n";
        PrintProj(Points[i]);
        cout << "\n";
    }

    // Run the algorithm
    cout << "\n";
    for (int i = 0; i < d-1; i++){
        cout << coef[i] << " * P[" << i+1 << "]   +   ";
    }
    cout << coef[d-1] << " * P[" << d << "] = \n";
    PrintAff(EdwardsToWeierAff(ProjToAff(Exponentiation(coef,EdwardsPoints))));

    cout << "(Output given in Weierstrauss form)\n\nTiming analysis (seconds):\n"
        << "T1( Edwards, " << n << ", " << d << ") = " << T1/1000.0 << "\n"
        << "T2( Edwards, " << n << ", " << d << ") = " << T2/1000.0 << "\n"
        << "T3( Edwards, " << n << ", " << d << ") = " << T3/1000.0 << "\n"
        << "T4( Edwards, " << n << ", " << d << ") = " << T4/1000.0 << "\n"
        << "Total time: " << (T1 + T2 + T3 + T4)/1000.0 << "\n\n"
        << "T1/(T3 + T4) = " << (T1 / (T3 + T4)) << "\n"
        << "(T1 + T3)/T4 = " << ((T1 + T3)/T4) << "\n\n";

    return 0;
}
