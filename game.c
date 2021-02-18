//------------------------------------------------------------------------------
//  game.c
//------------------------------------------------------------------------------

#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "sokol/sokol_time.h"
#include "sokol/sokol_app.h"
#include "sokol/sokol_gfx.h"
#include "sokol/sokol_glue.h"

#define LEN(arr) ((int) (sizeof arr / sizeof arr[0]))

void panic(char *msg) {
    fprintf(stderr, msg);
    sapp_request_quit();
}

#include "math.h"
#include "renderer.h"

#define BOARD_SIZE 10
#define HALF_BOARD (BOARD_SIZE / 2.0f)

/* stores input in between frames */
static struct {
    Vec2 mouse_pos;
} input;


/* A location on the game board
   can be thought of as a two dimensional vector of integers */
typedef struct {
    int x, y;
} Place;
Place place(int x, int y) {
    return (Place) { x, y };
}
/* compares equality between two places */
bool place_eq(Place a, Place b) {
    return a.x == b.x
        && a.y == b.y;
}
/* where the board is relative to the origin */
const Vec3 board_offset = { HALF_BOARD, 0.0, HALF_BOARD };
/* rounds a Vec3 to the nearest place on the board */
Place round_vec_to_place(Vec3 v) {
    v = add3(v, board_offset);
    return place((int) roundf(v.x), (int) roundf(v.z));
}
/* turns a Place into a Vec3 on the Y ground plane */
Vec3 place_to_vec(Place pl) {
    return sub3(vec3((f32) pl.x, 0.0f, (f32) pl.y), board_offset);
}
/* returns the euclidean distance between two places;
   diagonal distance is somewhat more than cardinal.
   useful for animations and making pathfinding look right, but
   for gameplay code, you probably want the octile distance. */
f32 euclid_dist(Place a, Place b) {
    return mag3(sub3(place_to_vec(a), place_to_vec(b)));
}
/* octile distance. good for gameplay code. */
int octile_dist(Place a, Place b) {
    return max(abs(a.x - b.x), abs(a.y - b.y));
}


/* Mostly used for the rendering code */
typedef enum {
    Art_Slot,
    Art_Pillar,
    Art_Player,
    Art_Goblin,
    Art_Target,
    Art_Sword,
} Art;


/* Weapons can be held by PieceKind_Mob,
   or made from PieceKind_Weapon */
typedef struct {
    Art art;
    int damage;
} Weapon;


/* Pieces occupy the game board and move around. */
#define MAX_PATH_STEPS 15
typedef enum { PieceKind_Weapon, PieceKind_Mob } PieceKind;
typedef enum {
    PieceAction_None,
    PieceAction_Move,
    PieceAction_Equip,
    PieceAction_Attack
} PieceAction;
typedef struct Piece Piece;
struct Piece {
    Art art;
    Place pos;
    f32 start_rot, rot, goal_rot, goal_rot_dur;

    /* when this is true, piece memory will not be reused */
    bool active;
    
    /* The action is set in the input phase
       and plays out in the animation phase */
    PieceAction action;
    /* PieceAction is the tag to this union */
    union {
        /* PieceAction_Move: */ struct {
            Place dest, path[MAX_PATH_STEPS];
            int path_steps;
        };
        /* PieceAction_Attack: */ Piece *target;
        /* PieceAction_Equip: */ struct {
            Piece *equip_item;
            Place equip_item_start_pos;
        };
    };

    PieceKind kind;
    /* PieceKind is the tag to this union */
    union {
        /* PieceKind_Weapon: */ int damage;
        /* PieceKind_Mob: */ struct {
            int hp;
            Weapon weapon;
            bool has_weapon;
        };
    };
};

/* NOTE: assumes (pc->kind == PieceKind_Weapon) */
Weapon piece_to_weapon(Piece *pc) {
    return (Weapon) {
        .art = pc->art,
        .damage = pc->damage,
    };
}

/* NOTE: assumes (pc->kind == PieceKind_Mob) */
void damage_piece(Piece *pc, Weapon *wep) {
    if (pc->hp <= wep->damage) {
        pc->active = false;
        pc->hp = 0;
    } else
        pc->hp -= wep->damage;
}

/* Returns the sum of the euclidean distances between
   each of the points in this piece's plotted path */
f32 path_dist(Piece *pc) {
    f32 total = 0.0;
    for (int p = 0; p < pc->path_steps; p++) {
        Place last = pc->path[p ? p - 1 : p];
        total += euclid_dist(pc->path[p], last);
    }
    return total;
}

Piece *piece_iter(Piece *pc);

/* Tiles make up the game board. */
typedef struct {
    Art art;
    bool blocked; /* Pieces cannot occupy blocked tiles */
} Tile;
Tile *tile_at_place(Place pl);


/* An A* implementation which stores the operative data on the stack.
   If successful, the resultant path is written into pathbuf and the
   length of the new path is returned. If a path cannot be found, 0
   is returned. */
int find_path(Place start, Place goal, Place pathbuf[MAX_PATH_STEPS]) {
    typedef struct Node Node;
    struct Node {
        bool fringe;
        f32 g_score, f_score;
        Node *came_from;
        Place pl;
    };
    #define NODES_LEN 100
    #define MAX_SCORE 50.0f
    Node nodes[NODES_LEN] = {0};
    nodes[0] = (Node) { true, 0.0f, 0.0f, NULL, start };
    int used_len = 1;

    Tile *goal_t = tile_at_place(goal);
    if (goal_t == NULL || goal_t->blocked) return 0;

    while (true) {
        /* find most viable fringe node (lowest f score) */
        f32 lowest_f_score = MAX_SCORE;
        int current_index = -1;
        for (int i = 0; i < used_len; i++)
            if (nodes[i].fringe && nodes[i].f_score <= lowest_f_score)
                lowest_f_score = nodes[i].f_score, current_index = i;

        /* if there are no fringe nodes, there is no path */
        if (current_index == -1) return 0;
        Node *current = &nodes[current_index];
        current->fringe = false;
        
        /* if this node is our goal, we have succeeded. */
        if (place_eq(current->pl, goal)) {
            int l = 0;
            /* fill pathbuf with came_from breadcrumbs */
            for (Node *c = current; c; l++, c = c->came_from) {
                /* pathbuf not large enough! */
                if (l == MAX_PATH_STEPS) return 0;
                pathbuf[l] = c->pl;
            }
            for (int e = l - 1, c = 0; c < l/2; e--, c++) {
                Place t = pathbuf[c];
                pathbuf[c] = pathbuf[e];
                pathbuf[e] = t;    
            }
            return l;
        }

        typedef enum { Dir_W, Dir_N, Dir_S, Dir_E, Dir_NE,
                       Dir_SE, Dir_NW, Dir_SW, Dir_Count } NeighborDir;
        for (NeighborDir n = 0; n < Dir_Count; n++) {
            Place neigh_pl;
            Place cpl = current->pl;
            switch (n) {
                case Dir_W:  neigh_pl = place(cpl.x + 1, cpl.y    ); break;
                case Dir_NW: neigh_pl = place(cpl.x + 1, cpl.y + 1); break;
                case Dir_SW: neigh_pl = place(cpl.x + 1, cpl.y - 1); break;
                case Dir_E:  neigh_pl = place(cpl.x - 1, cpl.y    ); break;
                case Dir_NE: neigh_pl = place(cpl.x - 1, cpl.y + 1); break;
                case Dir_SE: neigh_pl = place(cpl.x - 1, cpl.y - 1); break;
                case Dir_N:  neigh_pl = place(cpl.x    , cpl.y + 1); break;
                case Dir_S:  neigh_pl = place(cpl.x    , cpl.y - 1); break;
                default:     puts("Invalid NeighborDir variant");    break;
            }
            Node *neighbor = NULL;
            /* find the neighbor if already present */
            for (int i = 0; i < used_len; i++)
                if (place_eq(nodes[i].pl, neigh_pl))
                    neighbor = &nodes[i];
            /* otherwise grab another slot off of the node stack. */
            if (neighbor == NULL) {
                /* ran out of node space */
                if (used_len == NODES_LEN) return 0;

                neighbor = &nodes[used_len++];
                neighbor->pl = neigh_pl;
                /* starting with the maximum score here ensures updating below. */
                neighbor->g_score = MAX_SCORE;
                neighbor->f_score = MAX_SCORE;
            }

            f32 weight = euclid_dist(cpl, neigh_pl);
            Tile *neigh_t = tile_at_place(neigh_pl);
            if (neigh_t == NULL || neigh_t->blocked) weight = (f32) MAX_SCORE;
            else for (Piece *pc = 0; pc = piece_iter(pc);)
                if (!place_eq(pc->pos, goal) && place_eq(pc->pos, neigh_pl))
                    weight = (f32) MAX_SCORE;

            f32 tentative_g_score = current->g_score + weight;
            if (tentative_g_score < neighbor->g_score) {
                neighbor->came_from = current;
                neighbor->g_score = tentative_g_score;
                neighbor->f_score = neighbor->g_score + euclid_dist(neighbor->pl, goal);
                neighbor->fringe = true;
            }
        }
    }
}

/* mini state machine for interacting with pieces */
typedef enum {
    Interact_NeedsHover,
    Interact_NeedsNear,
    Interact_NeedsClick,
} Interact;

/* see start_input_phase and start_animation_phase */
typedef enum { Phase_Input, Phase_Animation } Phase;
typedef enum { AnimStage_None, AnimStage_Pieces, AnimStage_Camera } AnimStage;
#define MAX_PIECES 20
static struct {
    u64 start_time, last_render, anim_start;

    f64 dt, /* time since last render */
        elapsed; /* seconds since game started */

    f32 roll, /* goes from 0.0 to 1.0 every second */
        anim_dt, /* elapsed seconds of the current AnimStage */
        anim_pieces_dur, /* duration of this AnimStage_Pieces AnimStage */
        anim_camera_dur; /* duration of this AnimStage_Camera AnimStage */

    Vec3 cam, /* the point on the ground the camera points at */
         cam_start; /* point of reference for AnimStage_Camera */

    Phase phase;
    AnimStage anim_stage;

    Piece pieces[MAX_PIECES], *player, *hovered_piece;
    Interact hovered_interact;

    Tile tiles[BOARD_SIZE][BOARD_SIZE];
} world;

Piece *piece_iter(Piece *pc) {
    if (pc == NULL) pc = world.pieces - 1;

    while (!(++pc)->active)
        if ((pc - world.pieces) == MAX_PIECES)
            return NULL;

    if (pc->active) return pc;
    return NULL;
}

Tile *tile_at_place(Place pl) {
    if (pl.x >= BOARD_SIZE || pl.x < 0 || 
        pl.y >= BOARD_SIZE || pl.y < 0) return NULL;
    else return &world.tiles[pl.x][pl.y];
}

Piece *insert_piece(Place pl, Art art, PieceKind pk) {
    for (int i = 0; i < MAX_PIECES; i++) if (!world.pieces[i].active) {
        Piece *slot = &world.pieces[i];
        /* It's important to set the Piece's position and destination,
           so that it won't flock to the origin next animation phase. */
        *slot = (Piece) {
            .art = art,
            .kind = pk, 
            .pos = pl,
            .dest = pl,
            .path = {0},
            .active = true,
        };
        return slot;
    }
    puts("exceeded MAX_PIECES!");
    return NULL;
}

/* sokol-app calls this function when the application begins */
void init(void) {
    init_renderer();

    /* the RNG doesn't work with just 0 */
    srandf(9, 12, 32, 10);

    world.player = insert_piece(place(5, 5), Art_Player, PieceKind_Mob);
    world.player->hp = 5;
    insert_piece(place(5, 2), Art_Target, PieceKind_Mob)->hp = 3;
    insert_piece(place(4, 5), Art_Sword, PieceKind_Weapon)->damage = 1;
    for (int i = 2; i < 8; i++)
        world.tiles[i][3] = (Tile) { .art = Art_Pillar,
                                     .blocked = true };

    stm_setup();
    world.start_time = stm_now();
    world.last_render = stm_now();
}

static bool spawned_goblins;
void ai(void) {
    if (!spawned_goblins) {
        bool no_targets = true;
        for (Piece *pc = 0; pc = piece_iter(pc);)
            if (pc->art == Art_Target)
                no_targets = false;

        if (no_targets) {
            spawned_goblins = true;
            Piece *g1 = insert_piece(place(2, 2), Art_Goblin, PieceKind_Mob);
            Piece *g2 = insert_piece(place(7, 2), Art_Goblin, PieceKind_Mob);
            g1->hp = g2->hp = 3;
            Piece wep = { .art = Art_Sword, .damage = 1 };
            g1->weapon = g2->weapon = piece_to_weapon(&wep);
            g1->has_weapon = g2->has_weapon = true;
        }
    }

    for (Piece *pc = 0; pc = piece_iter(pc);)
        if (pc->art == Art_Goblin) {
            int to_player = octile_dist(pc->pos, world.player->pos);
            if (to_player > 1) {
                pc->path_steps = find_path(pc->pos, world.player->pos, pc->path);
                pc->path_steps = min(2, pc->path_steps);
                pc->dest = pc->path[pc->path_steps-1];
                pc->action = PieceAction_Move;
            } else if (world.player->action != PieceAction_Move) {
                pc->action = PieceAction_Attack;
                pc->target = world.player;
            }
        }
}

/* UPS = units per second */
#define PIECE_MOVING_UPS 3.0f
#define CAMERA_MOVING_UPS 5.0f
#define EQUIP_ANIMATION_DUR 0.5f
#define ATTACK_ANIMATION_DUR 1.0f
/* The animation phase moves the pieces along the board.
   The player cannot interact during this phase,
   but they can see the results of their actions.
   The beginning of the animation phase is where the enemy
   AI is done. The animation phase lasts a set amount of time. */
void start_animation_phase(void) {
    Piece *hpc = world.hovered_piece;
    /* you're clicking something that you're too far away from */
    if (hpc && world.hovered_interact == Interact_NeedsNear) return;
    if (hpc && world.hovered_interact == Interact_NeedsClick) {
        /* make sure the player doesn't move, they're
           interacting with something instead. */
        world.player->dest = world.player->pos;
        switch (hpc->kind) {
        case PieceKind_Weapon:;
            world.player->action = PieceAction_Equip;
            world.player->equip_item = hpc;
            world.player->equip_item_start_pos = hpc->pos;
            break;
        case PieceKind_Mob:;
            world.player->action = PieceAction_Attack;
            world.player->target = hpc;
            break;
        }
        world.hovered_piece = NULL;
    } else {
        /* not sure how else to handle out of bounds inputs */
        const Place center = { HALF_BOARD, HALF_BOARD };
        if (octile_dist(center, world.player->dest) >= HALF_BOARD+1) return;
        if (world.player->path_steps > 4) return;

        world.player->action = PieceAction_Move;
    }

    ai();

    world.phase = Phase_Animation;
    world.anim_stage = AnimStage_Pieces;
    world.anim_start = stm_now();

    /* we need to figure out what animation will take the longest
       so we know how long the animation phase needs to last. */
    f32 longest = 0.0f;
    world.anim_camera_dur = 0.0f;
    for (Piece *pc = 0; pc = piece_iter(pc);) {
        f32 duration = 0.0f;
        Place *target = NULL;

        switch (pc->action) {
        case PieceAction_Move:;
            /* it's assumed that the path is already calculated */
            duration = path_dist(pc) / PIECE_MOVING_UPS;

            /* plus time for moving the camera to where the player is now */
            if (pc == world.player) {
                Vec3 start = place_to_vec(pc->pos), end = place_to_vec(pc->dest);
                f32 direct_dist = mag3(sub3(start, end));
                world.anim_camera_dur = direct_dist / CAMERA_MOVING_UPS;
            }

            /* some extra time may be needed to turn around
               if the path points in a different direction */
            target = &pc->path[1];
            break;
        case PieceAction_Equip:;
            duration = EQUIP_ANIMATION_DUR;

            /* some extra time may be needed to rotate
               to look at what's being picked up */
            target = &pc->equip_item->pos;
            break;
        case PieceAction_Attack:;
            duration = ATTACK_ANIMATION_DUR;
            /* some extra time may be needed
               to rotate to look at the target */
            target = &pc->target->pos;
            break;
        }

        pc->start_rot = pc->rot;
        if (target) {
            Vec3     pos = place_to_vec(pc->pos),
                 look_at = place_to_vec(*target);
            f32 goal = atan2(pos.x - look_at.x, pos.z - look_at.z) + PI32/2.0f;
            Vec2 goal2 = vec2(   cosf(goal), sinf(goal)),
                  now2 = vec2(cosf(pc->rot), sinf(pc->rot));
            /* delta will be 0.0f if they are parallel, and 1.0f if perpendicular */
            f32 dot = dot2(goal2, now2);
            f32 delta = (1.0f - dot) / 2.0f;
            pc->goal_rot_dur = delta;
            pc->goal_rot = goal;
            duration += delta;
        } else {
            pc->goal_rot_dur = 0.0f;
        }

        longest = fmaxf(longest, duration);
    }
    world.anim_pieces_dur = longest;
}

/* The input phase lasts an indefinite amount of time,
   ending when the player clicks.
   Some things are rendered in the input phase that are not
   rendered in the animation phase, to help the player make
   intelligent gameplay decisions. */
void start_input_phase(void) {
    for (Piece *pc = 0; pc = piece_iter(pc);)
        pc->action = PieceAction_None;
    world.phase = Phase_Input;
    world.anim_stage = AnimStage_None;
}

/* this function is called every frame. it increments anim_dt,
   and steps the animation stage, if necessary. */
void update_anim_stage(void) {
    world.anim_dt = (f32) stm_sec(stm_since(world.anim_start));
    switch (world.anim_stage) {
    case (AnimStage_Pieces):;
        if (world.anim_dt > world.anim_pieces_dur) {
            world.anim_stage = AnimStage_Camera;
            world.cam_start = world.cam;
            world.anim_start = stm_now();

            /* here we finalize what the animations expressed to the player */
            for (Piece *pc = 0; pc = piece_iter(pc);)
                switch (pc->action) {
                case PieceAction_Move:
                    pc->pos = pc->dest;
                    break;
                case PieceAction_Equip:
                    /* the item is parented to its holder at the beginning
                       of the animation phase, not the end */
                    break;
                case PieceAction_Attack:
                    damage_piece(pc->target, &pc->weapon);
                    break;
                }
        }
        break;
    case (AnimStage_Camera):;
        if (world.anim_camera_dur > 0.0f) {
            Vec3 cam_goal = place_to_vec(world.player->pos);
            f32 t = world.anim_dt / world.anim_camera_dur;
            world.cam = lerp3(world.cam_start, t, cam_goal);
        }
        if (world.anim_dt > world.anim_camera_dur)
            start_input_phase();
        break;
    default:;
        world.anim_dt = 0.0;
        break;
    }
}

/* sokol-app calls this function when some input is received
   from the host operating system */
void event(const sapp_event *ev) { switch (ev->type) {
    case SAPP_EVENTTYPE_MOUSE_DOWN:;
        if (world.phase == Phase_Input)
            start_animation_phase();
    case SAPP_EVENTTYPE_MOUSE_UP:;
    case SAPP_EVENTTYPE_MOUSE_MOVE:;
        input.mouse_pos = vec2(ev->mouse_x, ev->mouse_y);
        break;
    case SAPP_EVENTTYPE_KEY_DOWN:;
        #ifndef NDEBUG
            if (ev->key_code == SAPP_KEYCODE_ESCAPE)
                sapp_request_quit();
        #endif
        break;
    default:;
        break;
    }
}

/* Returns the Place on the game board that the mouse is under.
   This implicitly relies on the renderer's view projection matrix. */
const Vec3 eye = { 4.5f, 8.5f, 4.5f };
Place place_under_mouse(void) {
    const Ray ground_plane = { .origin = vec3f(0.0), .vector = vec3_y() };
    Ray mouse_ray;
    mouse_ray.origin = add3(eye, world.cam);
    mouse_ray.vector = sub3(mouse_ray.origin, unproject(input.mouse_pos));
    return round_vec_to_place(ray_hit_plane(mouse_ray, ground_plane));
}

/* Decides based on where the mouse is if the player is trying to
   move somewhere or interact with a piece, and makes the necessary
   state changes to visualize that for the player. */
void process_input(void) {
    Place mouse = place_under_mouse();

    world.hovered_piece = NULL;
    for (Piece *pc = 0; pc = piece_iter(pc);)
        if (pc != world.player && place_eq(pc->pos, mouse)) {
            world.hovered_piece = pc;
            if (octile_dist(pc->pos, world.player->pos) <= 1)
                world.hovered_interact = Interact_NeedsClick;
            else world.hovered_interact = Interact_NeedsNear;
            /* prevent path visualization from being rendered */
            world.player->path_steps = 0;
            break;
        }

    if (world.hovered_piece == NULL) {
        Piece *pc = world.player;
        pc->path_steps = find_path(pc->pos, mouse, pc->path);
        pc->dest = pc->path[pc->path_steps-1];
    }
}

/* Constructs a four dimensional matrix from
   position, scale, and rotation components */
Mat4 pos_scale_rot4x4(Vec3 pos, Vec3 scale, Vec3 rot) {
    Mat4 mat = translate4x4(pos);
    mat = mul4x4(mat, ypr4x4(rot.x, rot.y, rot.z));
    mat = mul4x4(mat, scale4x4(scale));
    return mat;
}

/* Work in progress pen abstraction for changing the way
   things are rendered via implicit context. */
typedef struct {
    f32 scalef;
    const Vec4 *color;
    MaterialKind kind;
} Material;
static Material pen = { 1.0f, NULL, MaterialKind_Normal };
void set_default_pen() { pen = (Material) { 1.0f, NULL, MaterialKind_Normal }; }

void draw_art(Art art, Mat4 mat) {
    Vec3 scale = vec3f(0.3 * pen.scalef);
    Vec4 color;
    if (pen.color) color = *pen.color;
    else switch (art) {
    case Art_Pillar:;
    case Art_Slot:;
        color = vec4(0.37f, 0.25f, 0.50f, 1.00f); break;
    case Art_Goblin:;
        color = vec4(0.37f, 0.50f, 0.25f, 1.00f); break;
    case Art_Sword:;
        color = vec4(0.47f, 0.35f, 0.50f, 1.00f); break;
    case Art_Player:;
        color = vec4(0.29f, 0.22f, 0.18f, 1.00f); break;
    case Art_Target:;
        color = vec4(0.80f, 0.75f, 0.80f, 1.00f); break;
    default:;
        puts("Invalid Art variant");
        color = vec4(0.38f, 0.54f, 0.33f, 1.00f); break;
    };
    Vec3 rot, pos = vec3f(0.0);

    switch (art) {
    case Art_Slot:;
        if (pen.kind == MaterialKind_Normal)
            color.w = fminf(color.w, 0.15f);
        scale.y *= 0.2f;
        mat = mul4x4(mat, pos_scale_rot4x4(pos, scale, vec3f(0.0f)));
        draw_asset(mat, ASSET_CYLINDER, color, MaterialKind_Ghost);
        break;
    case Art_Pillar:;
        scale = mul3(scale, vec3(1.3f, 2.0f, 1.3f));
        pos.y += scale.y / 2.0f;
        mat = mul4x4(mat, pos_scale_rot4x4(pos, scale, vec3f(0.0f)));
        draw_asset(mat, ASSET_CYLINDER, color, pen.kind);
        break;
    case Art_Target:;
        scale.y *= 0.4f;
        pos.y += scale.z;
        rot = vec3(0.0f, 0.0f, PI32/2.0f);
        Mat4 outer = mul4x4(mat, pos_scale_rot4x4(pos, scale, rot));
        draw_asset(outer, ASSET_CYLINDER, color, pen.kind);

        scale = mul3(scale, vec3(0.8f, 1.1f, 0.8f));
        Mat4 middle = mul4x4(mat, pos_scale_rot4x4(pos, scale, rot));
        color.x -= 0.4f;
        color.y -= 0.3f;
        color.z -= 0.4f;
        draw_asset(middle, ASSET_CYLINDER, color, pen.kind);
        
        scale = mul3(scale, vec3(0.5f, 1.1f, 0.5f));
        Mat4 inner = mul4x4(mat, pos_scale_rot4x4(pos, scale, rot));
        color.y -= 0.3f;
        color.z -= 0.3f;
        draw_asset(inner, ASSET_CYLINDER, color, pen.kind);
        break;
    case Art_Sword:;
        scale = mul3(scale, vec3(0.15f, 2.75f, 0.15f));
        pos.y += scale.x / 2.0f;

        rot = vec3(0.0f, 0.0f, PI32/2.0f);
        Mat4 temp = mul4x4(mat, pos_scale_rot4x4(pos, scale, rot));
        draw_asset(temp, ASSET_CYLINDER, color, pen.kind);

        scale = mul3(scale, vec3(0.8f, 0.25f, 0.8f));
        pos.x += 0.135f;
        rot.x = rot.z;
        temp = mul4x4(mat, pos_scale_rot4x4(pos, scale, rot));
        draw_asset(temp, ASSET_CYLINDER, color, pen.kind);
        break;
   case Art_Goblin:;
   case Art_Player:;
        pos.y = 0.5f;
        scale = mul3f(scale, 1.3f);
        mat = mul4x4(mat, pos_scale_rot4x4(pos, scale, vec3f(0.0f)));

        draw_asset(mat, ASSET_ICOSAHEDRON, color, pen.kind);
        break;
    default:;
        puts("unknown Art variant");
        break;
    }
}

const Vec4 path_colors[2][2] = {
    /* in bounds */                    /* out of bounds */
    {{ 0.30f, 0.30f, 0.80f, 0.30f }, { 0.10f, 0.10f, 0.80f, 0.10f }},/* path */
    {{ 0.30f, 0.80f, 0.30f, 0.30f }, { 0.80f, 0.10f, 0.10f, 0.10f }} /* end  */
};
void draw_path(Place *path, int path_steps) {
    /* the idea here is to render the orbs at each step in the path, and
       over the course of a second move them closer and closer to the next
       step, so that it looks as if each orb goes across the entire path,
       because the next orb picks up right where the last left off. */
    for (int i = 0; i < path_steps; i++) {
        Vec3 pos;
        if (i == 0) pos = place_to_vec(path[path_steps-1]);
        else pos = lerp3(place_to_vec(path[i ? i-1 : i]),
                         world.roll,
                         place_to_vec(path[i]));
        pos.y += 0.3f;
        Mat4 mat = pos_scale_rot4x4(pos, vec3f(0.3f), vec3f(world.elapsed));

        Vec4 color = path_colors[i == 0][(i ? i : (path_steps-1)) > 3];
        draw_asset(mat, ASSET_ICOSAHEDRON, color, MaterialKind_Ghost);
    }
}

void draw_tiles(void) {
    for (int x = 0; x < BOARD_SIZE; x++)
    for (int y = 0; y < BOARD_SIZE; y++) {
        Place pl = place(x, y);
        Tile *tile = tile_at_place(pl);
        draw_art(tile->art, translate4x4(place_to_vec(pl)));
    }
}

/* animates the movement of a Piece where pc->kind == PieceKind_Mob.
   modifies the piece's rotation and position for a single frame of
   its movement, decided based on the t parameter. if t is 0.0f, the
   first frame is created, if t is 1.0f, the last frame is created. */
void animated_mob_move(Piece *pc, f32 t, Vec3 *pos) {
    /* the idea here is to use `progress` to find the tiles we
       should be between, then use that same variable to put us
       an appropriate amount between those two tiles. */
    f32 progress = fminf(t, path_dist(pc) / PIECE_MOVING_UPS);

    /* last_rot is either the rotation from the previous step,
       or if there is no previous step, where the Piece needs to
       look in order to point toward path[1] from path[0]. */
    f32 last_rot = pc->goal_rot;
    for (int p = 0; p < pc->path_steps; p++) {
        Place here = pc->path[p], next = pc->path[p + 1];
        f32 angle = PI32/2.0f + atan2(here.x - next.x, here.y - next.y),
            duration = euclid_dist(here, next) / PIECE_MOVING_UPS;
        if (progress < duration) {
            f32 t = progress / duration;
            pc->rot = lerp_rad(last_rot, fminf(t / 0.2f, 1.0f), angle);
            *pos = lerp3(place_to_vec(here), t, place_to_vec(next));
            return;
        }
        progress -= duration;
        last_rot = angle;
    }
}

Quat weapon_rotation(f32 x, f32 y) {
    return mulQ(axis_angleQ(vec3_x(), y),
                axis_angleQ(vec3_y(), x));
}
/* modifies a Piece's hand position and weapon rotation
   based on the t parameter to create a single frame
   in an attack animation. if t is 0.0f, the first frame
   is created, if t is 1.0f, the last frame is created. */
void animated_attack(Piece *pc, f32 t, Vec3 *hand, Quat *wep_rot) {
    /* Same idea as animated_mob_pos, we're just finding
       the right frame to use instead of the right node,
       and the results are applied to the weapon. */
    f32 progress = fminf(t, ATTACK_ANIMATION_DUR);

    typedef struct {
        f32 duration;
        Quat rot;
        Vec3 pos;
    } KeyFrame;

    KeyFrame default_kf = { 0.0f, identQ(), vec3f(0.0f) };
    const KeyFrame keyframes[] = {
        {2.0f, weapon_rotation( 0.0f, 1.4f), {0.00f, 0.00f,  0.00f}},/* move to left   */
        {2.8f, weapon_rotation(-0.8f, 1.4f), {0.40f, 0.00f, -0.10f}},/* wind up        */
        {1.0f, weapon_rotation( 1.0f, 1.8f), {0.40f, 0.00f,  0.80f}},/* swing          */
        {2.0f, weapon_rotation( 1.5f, 2.1f), {0.20f, 0.00f,  0.40f}},/* follow through */
        {2.0f, weapon_rotation( 0.0f, 0.0f), {0.00f, 0.00f,  0.00f}},/* back home      */
    };

    f32 total = 0.0;
    for (int i = 0; i < LEN(keyframes); i++)
        total += keyframes[i].duration;

    for (int i = 0; i < LEN(keyframes); i++) {
        KeyFrame next = keyframes[i],
        last = i == 0 ? default_kf : keyframes[i - 1];
        f32 duration = (next.duration / total) * ATTACK_ANIMATION_DUR;
        if (progress <= duration) {
            f32 t = progress / duration;
            *wep_rot = mulQ(*wep_rot, slerpQ(last.rot, t, next.rot));
            *hand = add3(*hand, lerp3(last.pos, t, next.pos));
            break;
        }
        progress -= duration;
    }
}

void draw_piece(Piece *pc) {
    Vec3 hand = vec3(0.3f, 0.5f, -0.375f);
    Quat wep_rot = yprQ(0.0f, PI32/2.0f, PI32);
    Vec3 pos = place_to_vec(pc->pos);

    f32 t = world.anim_dt;
    if (pc->kind == PieceKind_Mob) {

        if (world.anim_stage == AnimStage_Pieces && pc->action != PieceAction_None) {
            if (t < pc->goal_rot_dur)
                pc->rot = lerp_rad(pc->start_rot, t / pc->goal_rot_dur, pc->goal_rot);
            t -= pc->goal_rot_dur;

            if (t > 0.0f)
                switch (pc->action) {
                case PieceAction_Move:;
                    animated_mob_move(pc, t, &pos);
                    break;
                case PieceAction_Attack:;
                    animated_attack(pc, t, &hand, &wep_rot);
                    break;
                case PieceAction_Equip:;
                    /* deactivate the weapon and make it the holder's responsibility
                       as soon as the equip animation starts. */
                    if (pc->equip_item->active) {
                        pc->equip_item->active = false;
                        pc->weapon = piece_to_weapon(pc->equip_item);
                        pc->has_weapon = true;
                    }
                }
        }

        const Vec4 health_color = {0.0f, 1.0f, 0.0f, 0.25f};
        for (int i = 0; i < pc->hp; i++) {
            f32 r = (f32) i / (f32) pc->hp * (PI32*2.0f) + world.elapsed;
            Vec3 p = add3(pos, mul3f(vec3(cosf(r), 0.1f, sinf(r)), 0.4f));
            Mat4 mat = pos_scale_rot4x4(p, vec3f(0.1f), vec3f(world.elapsed));
            draw_asset(mat, ASSET_ICOSAHEDRON, health_color, MaterialKind_Ghost);
        }
    }

    Mat4 mat = mul4x4(translate4x4(pos), ypr4x4(pc->rot, 0.0f, 0.0f));
    if (pc->kind == PieceKind_Mob) {
        if (pc->has_weapon) {
            if (pc->action == PieceAction_Equip && t > 0.0f) {
                f32 equip_t = fminf(t, EQUIP_ANIMATION_DUR) / EQUIP_ANIMATION_DUR;
                Vec3 start_world = place_to_vec(pc->equip_item_start_pos),
                     start_local = mul3f(vec3_x(), mag3(sub3(start_world, pos)));
                hand = lerp3(start_local, equip_t, hand);
                wep_rot = slerpQ(mat4Q(invert4x4(mat)), equip_t, wep_rot);
            }
            Mat4 wep = mul4x4(translate4x4(hand), quat4x4(wep_rot));
            draw_art(pc->weapon.art, mul4x4(mat, wep));
        }
    }

    /* highlighting hovered pieces */
    if (world.phase == Phase_Input && world.hovered_piece == pc) {
        const Vec4  needs_near_color = vec4(1.00f, 0.00f, 0.00f, 0.25f),
                   needs_click_color = vec4(0.00f, 1.00f, 0.00f, 0.25f);
        pen.scalef = 1.4;

        switch (world.hovered_interact) {
        case Interact_NeedsClick:;
            pen.color = &needs_click_color;
            break;
        case Interact_NeedsNear:;
            pen.color = &needs_near_color;
            Vec3  start = place_to_vec(pc->pos),
                    end = place_to_vec(world.player->pos),
                 center = div3f(add3(start, end), 2.0f);
            f32 angle = atan2(end.x - start.x, end.z - start.z) + PI32/2.0f;
            center.y += 0.2f;
            Vec3 rot = vec3(angle, 0.0f, PI32/2.0f);
            Vec3 scale = vec3(0.04f, mag3(sub3(start, end)) - 1.0f, 0.04f);
            draw_asset(pos_scale_rot4x4(center, scale, rot),
                       ASSET_CYLINDER,
                       needs_near_color,
                       MaterialKind_Ghost);
            break;
        default:
            puts("impossible Interact variant");
            break;
        }
        pen.kind = MaterialKind_Ghost;
        draw_art(pc->art, translate4x4(pos));
        set_default_pen();
    }

    draw_art(pc->art, mat);
}

void frame(void) {
    if (world.phase == Phase_Input)
        process_input();

    start_render(look_at4x4(add3(world.cam, eye), world.cam, vec3_y()));
    if (world.phase == Phase_Input)
        draw_path(world.player->path, world.player->path_steps);
    draw_tiles();
    for (Piece *pc = 0; pc = piece_iter(pc);)
        draw_piece(pc);
    end_render();

    world.dt = stm_sec(stm_since(world.last_render));
    world.roll = wrap(world.roll + (f32) world.dt, 1.0f);
    world.elapsed = stm_sec(stm_since(world.start_time));
    update_anim_stage();

    world.last_render = stm_now();
}

void cleanup(void) {
    sg_shutdown();
}

sapp_desc sokol_main(int argc, char *argv[]) {
    (void)argc;
    (void)argv;

    return (sapp_desc) {
        .init_cb = init,
        .frame_cb = frame,
        .cleanup_cb = cleanup,
        .event_cb = event,
        .width = 1280,
        .height = 720,
        .sample_count = 4,
        .gl_force_gles2 = true,
        .window_title = "sandsphere",
    };
}
